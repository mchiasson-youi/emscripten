/*
 * Copyright 2019 The Emscripten Authors.  All rights reserved.
 * Emscripten is available under two separate licenses, the MIT license and the
 * University of Illinois/NCSA Open Source License.  Both these licenses can be
 * found in the LICENSE file.
 */

#include <assert.h>
#include <stdbool.h>
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <malloc.h>
#include <time.h>
#include <unistd.h>
#include <sysexits.h>

#include <emscripten.h>
#include <emscripten/heap.h>
#include <wasi/api.h>
#include <wasi/wasi-helpers.h>

#include "lock.h"

/*
 * WASI support code. These are compiled with the program, and call out
 * using wasi APIs, which can be provided either by a wasi VM or by our
 * emitted JS.
 */

// libc

void abort() {
  _Exit(1);
}

_Static_assert(CLOCK_REALTIME == __WASI_CLOCKID_REALTIME, "must match");
_Static_assert(CLOCK_MONOTONIC == __WASI_CLOCKID_MONOTONIC, "must match");
_Static_assert(CLOCK_PROCESS_CPUTIME_ID == __WASI_CLOCKID_PROCESS_CPUTIME_ID, "must match");
_Static_assert(CLOCK_THREAD_CPUTIME_ID == __WASI_CLOCKID_THREAD_CPUTIME_ID, "must match");

#define NSEC_PER_SEC (1000 * 1000 * 1000)

struct timespec __wasi_timestamp_to_timespec(__wasi_timestamp_t timestamp) {
  return (struct timespec){.tv_sec = timestamp / NSEC_PER_SEC,
                           .tv_nsec = timestamp % NSEC_PER_SEC};
}

typedef struct preopen {
    /// The path prefix associated with the file descriptor.
    const char *prefix;

    /// The file descriptor.
    __wasi_fd_t fd;
} preopen;

/// A simple growable array of `preopen`.
static preopen *preopens = NULL;
static size_t num_preopens = 0;
static size_t preopen_capacity = 0;

char *__wasilibc_cwd = "/";

// WASI syscalls should just return ENOTDIR if that's what the problem is.
static inline __wasi_errno_t errno_fixup_directory(__wasi_fd_t fd,
                                                     __wasi_errno_t error) {
  return error;
}

#ifdef NDEBUG
#define assert_invariants() // assertions disabled
#else
static void assert_invariants(void) {
    assert(num_preopens <= preopen_capacity);
    assert(preopen_capacity == 0 || preopens != NULL);
    assert(preopen_capacity == 0 ||
           preopen_capacity * sizeof(preopen) > preopen_capacity);

    for (size_t i = 0; i < num_preopens; ++i) {
        const preopen *pre = &preopens[i];
        assert(pre->prefix != NULL);
        assert(pre->fd != (__wasi_fd_t)-1);
#ifdef __wasm__
        assert((uintptr_t)pre->prefix <
               (__uint128_t)__builtin_wasm_memory_size(0) * PAGESIZE);
#endif
    }
}
#endif

/// Allocate space for more preopens. Returns 0 on success and -1 on failure.
static int resize(void) {
    size_t start_capacity = 4;
    size_t old_capacity = preopen_capacity;
    size_t new_capacity = old_capacity == 0 ? start_capacity : old_capacity * 2;

    preopen *old_preopens = preopens;
    preopen *new_preopens = calloc(sizeof(preopen), new_capacity);
    if (new_preopens == NULL)
        return -1;

    memcpy(new_preopens, old_preopens, num_preopens * sizeof(preopen));
    preopens = new_preopens;
    preopen_capacity = new_capacity;
    free(old_preopens);

    assert_invariants();
    return 0;
}

// Normalize an absolute path. Removes leading `/` and leading `./`, so the
// first character is the start of a directory name. This works because our
// process always starts with a working directory of `/`. Additionally translate
// `.` to the empty string.
static const char *strip_prefixes(const char *path) {
    while (1) {
        if (path[0] == '/') {
            path++;
        } else if (path[0] == '.' && path[1] == '/') {
            path += 2;
        } else if (path[0] == '.' && path[1] == 0) {
            path++;
        } else {
            break;
        }
    }

    return path;
}

/// Register the given preopened file descriptor under the given path.
///
/// This function takes ownership of `prefix`.
static int internal_register_preopened_fd(__wasi_fd_t fd, const char *relprefix) {
    // Check preconditions.
    assert_invariants();
    assert(fd != AT_FDCWD);
    assert(fd != -1);
    assert(relprefix != NULL);

    if (num_preopens == preopen_capacity && resize() != 0)
        return -1;

    char *prefix = strdup(strip_prefixes(relprefix));
    if (prefix == NULL)
        return -1;
    preopens[num_preopens++] = (preopen) { prefix, fd, };

    assert_invariants();
    return 0;
}

static void __wasilibc_populate_preopens(void) {
    // Skip stdin, stdout, and stderr, and count up until we reach an invalid
    // file descriptor.
    for (__wasi_fd_t fd = 3; fd != 0; ++fd) {
        __wasi_prestat_t prestat;
        __wasi_errno_t ret = __wasi_fd_prestat_get(fd, &prestat);
        if (ret == __WASI_ERRNO_BADF)
            break;
        if (ret != __WASI_ERRNO_SUCCESS)
            goto oserr;
        switch (prestat.pr_type) {
        case __WASI_PREOPENTYPE_DIR: {
            char *prefix = malloc(prestat.u.dir.pr_name_len + 1);
            if (prefix == NULL)
                goto software;

            // TODO: Remove the cast on `path` once the witx is updated with
            // char8 support.
            ret = __wasi_fd_prestat_dir_name(fd, (uint8_t *)prefix,
                                             prestat.u.dir.pr_name_len);
            if (ret != __WASI_ERRNO_SUCCESS)
                goto oserr;
            prefix[prestat.u.dir.pr_name_len] = '\0';

            if (internal_register_preopened_fd(fd, prefix) != 0)
                goto software;
            free(prefix);

            break;
        }
        default:
            break;
        }
    }

    return;
oserr:
    _Exit(EX_OSERR);
software:
    _Exit(EX_SOFTWARE);
}

/// Are the `prefix_len` bytes pointed to by `prefix` a prefix of `path`?
static bool prefix_matches(const char *prefix, size_t prefix_len, const char *path) {
    // Allow an empty string as a prefix of any relative path.
    if (path[0] != '/' && prefix_len == 0)
        return true;

    // Check whether any bytes of the prefix differ.
    if (memcmp(path, prefix, prefix_len) != 0)
        return false;

    // Ignore trailing slashes in directory names.
    size_t i = prefix_len;
    while (i > 0 && prefix[i - 1] == '/') {
        --i;
    }

    // Match only complete path components.
    char last = path[i];
    return last == '/' || last == '\0';
}

static const char *make_absolute(const char *path) {
    static char *make_absolute_buf = NULL;
    static size_t make_absolute_len = 0;

    // If this path is absolute, then we return it as-is.
    if (path[0] == '/') {
        return path;
    }

    // If the path is empty, or points to the current directory, then return
    // the current directory.
    if (path[0] == 0 || !strcmp(path, ".") || !strcmp(path, "./")) {
        return __wasilibc_cwd;
    }

    // If the path starts with `./` then we won't be appending that to the cwd.
    if (path[0] == '.' && path[1] == '/')
        path += 2;

    // Otherwise we'll take the current directory, add a `/`, and then add the
    // input `path`. Note that this doesn't do any normalization (like removing
    // `/./`).
    size_t cwd_len = strlen(__wasilibc_cwd);
    size_t path_len = strlen(path);
    int need_slash = __wasilibc_cwd[cwd_len - 1] == '/' ? 0 : 1;
    size_t alloc_len = cwd_len + path_len + 1 + need_slash;
    if (alloc_len > make_absolute_len) {
        make_absolute_buf = realloc(make_absolute_buf, alloc_len);
        if (make_absolute_buf == NULL)
            return NULL;
        make_absolute_len = alloc_len;
    }
    strcpy(make_absolute_buf, __wasilibc_cwd);
    if (need_slash)
        strcpy(make_absolute_buf + cwd_len, "/");
    strcpy(make_absolute_buf + cwd_len + need_slash, path);
    return make_absolute_buf;
}

// See the documentation in libc-find-relpath.h.
int __wasilibc_find_abspath(const char *path,
                            const char **abs_prefix,
                            const char **relative_path) {

    // MATTC: Lazy pre-loaded. (hilarious!)
    if(num_preopens == 0) { __wasilibc_populate_preopens(); }

    // Strip leading `/` characters, the prefixes we're mataching won't have
    // them.
    while (*path == '/')
        path++;
    // Search through the preopens table. Iterate in reverse so that more
    // recently added preopens take precedence over less recently addded ones.
    size_t match_len = 0;
    int fd = -1;
    for (size_t i = num_preopens; i > 0; --i) {
        const preopen *pre = &preopens[i - 1];
        const char *prefix = pre->prefix;
        size_t len = strlen(prefix);

        // If we haven't had a match yet, or the candidate path is longer than
        // our current best match's path, and the candidate path is a prefix of
        // the requested path, take that as the new best path.
        if ((fd == -1 || len > match_len) &&
            prefix_matches(prefix, len, path))
        {
            fd = pre->fd;
            match_len = len;
            *abs_prefix = prefix;
        }
    }

    if (fd == -1) {
        errno = ENOENT;
        return -1;
    }

    // The relative path is the substring after the portion that was matched.
    const char *computed = path + match_len;

    // Omit leading slashes in the relative path.
    while (*computed == '/')
        ++computed;

    // *at syscalls don't accept empty relative paths, so use "." instead.
    if (*computed == '\0')
        computed = ".";

    *relative_path = computed;
    return fd;
}

// Helper function defined only in this object file and weakly referenced from
// `preopens.c` and `posix.c` This function isn't necessary unless `chdir` is
// pulled in because all paths are otherwise absolute or relative to the root.
int __wasilibc_find_relpath_alloc(
    const char *path,
    const char **abs_prefix,
    char **relative_buf,
    size_t *relative_buf_len,
    int can_realloc
) {
    // First, make our path absolute taking the cwd into account.
    const char *abspath = make_absolute(path);
    if (abspath == NULL) {
        errno = ENOMEM;
        return -1;
    }

    // Next use our absolute path and split it. Find the preopened `fd` parent
    // directory and set `abs_prefix`. Next up we'll be trying to fit `rel`
    // into `relative_buf`.
    const char *rel;
    int fd = __wasilibc_find_abspath(abspath, abs_prefix, &rel);
    if (fd == -1)
        return -1;

    size_t rel_len = strlen(rel);
    if (*relative_buf_len < rel_len + 1) {
        if (!can_realloc) {
            errno = ERANGE;
            return -1;
        }
        char *tmp = realloc(*relative_buf, rel_len + 1);
        if (tmp == NULL) {
            errno = ENOMEM;
            return -1;
        }
        *relative_buf = tmp;
        *relative_buf_len = rel_len + 1;
    }
    strcpy(*relative_buf, rel);
    return fd;
}

// See the documentation in libc-find-relpath.h.
int __wasilibc_find_relpath(const char *path,
                            const char **abs_prefix,
                            char **relative_path,
                            size_t relative_path_len) {
    return __wasilibc_find_relpath_alloc(path, abs_prefix, relative_path, &relative_path_len, 0);
}

static int find_relpath2(
    const char *path,
    char **relative,
    size_t *relative_len
) {
    // See comments in `preopens.c` for what this trick is doing.
    const char *abs;
    return __wasilibc_find_relpath_alloc(path, &abs, relative, relative_len, 1);
}

// Helper to call `__wasilibc_find_relpath` and return an already-managed
// pointer for the `relative` path. This function is not reentrant since the
// `relative` pointer will point to static data that cannot be reused until
// `relative` is no longer used.
static int find_relpath(const char *path, char **relative) {
    static __thread char *relative_buf = NULL;
    static __thread size_t relative_buf_len = 0;
    *relative = relative_buf;
    return find_relpath2(path, relative, &relative_buf_len);
}

int clock_getres(clockid_t clk_id, struct timespec *tp) {
  // See https://github.com/bytecodealliance/wasmtime/issues/3714
  if (clk_id > __WASI_CLOCKID_THREAD_CPUTIME_ID || clk_id < 0) {
    errno = EINVAL;
    return -1;
  }
  __wasi_timestamp_t res;
  __wasi_errno_t error = __wasi_clock_res_get(clk_id, &res);
  if (error != __WASI_ERRNO_SUCCESS) {
    return __wasi_syscall_ret(error);
  }
  *tp = __wasi_timestamp_to_timespec(res);
  return 0;
}

// mmap support is nonexistent. TODO: emulate simple mmaps using
// stdio + malloc, which is slow but may help some things?

const unsigned char * __map_file(const char *pathname, size_t *size) {
  errno = ENOSYS;
  return NULL;
}

long _mmap_js(long addr, long length, long prot, long flags, long fd, long offset, int* allocated) {
  return -ENOSYS;
}

long _munmap_js(long addr, long length, long prot, long flags, long fd, long offset) {
  return -ENOSYS;
}

// open(), etc. - we just support the standard streams, with no
// corner case error checking; everything else is not permitted.
// TODO: full file support for WASI, or an option for it
// open()
// Mark this as weak so that wasmfs does not collide with it. That is, if wasmfs
// is in use, we want to use that and not this.
__attribute__((__weak__))
long __syscall_open(const char* path, long flags, ...) {
    if (!strcmp(path, "/dev/stdin")) return STDIN_FILENO;
    if (!strcmp(path, "/dev/stdout")) return STDOUT_FILENO;
    if (!strcmp(path, "/dev/stderr")) return STDERR_FILENO;

    char *relative_path;
    int fd = find_relpath(path, &relative_path);

    // If we can't find a preopen for it, indicate that we lack capabilities.
    if (fd == -1)
    {
        errno = __WASI_ERRNO_NOTCAPABLE;
        return -1;
    }

    // Compute rights corresponding with the access modes provided.
    // Attempt to obtain all rights, except the ones that contradict the
    // access mode provided to openat().
    __wasi_rights_t max =
        ~(__WASI_RIGHTS_FD_DATASYNC | __WASI_RIGHTS_FD_READ |
          __WASI_RIGHTS_FD_WRITE | __WASI_RIGHTS_FD_ALLOCATE |
          __WASI_RIGHTS_FD_READDIR | __WASI_RIGHTS_FD_FILESTAT_SET_SIZE);

    switch (flags & O_ACCMODE)
    {
        case O_RDONLY:
            max |= __WASI_RIGHTS_FD_READ | __WASI_RIGHTS_FD_READDIR;
            break;
        case O_WRONLY:
            max |=  __WASI_RIGHTS_FD_DATASYNC | __WASI_RIGHTS_FD_WRITE |
                    __WASI_RIGHTS_FD_ALLOCATE |
                    __WASI_RIGHTS_FD_FILESTAT_SET_SIZE;
            break;
        case O_RDWR:
            max |=  __WASI_RIGHTS_FD_READ | __WASI_RIGHTS_FD_READDIR |
                    __WASI_RIGHTS_FD_DATASYNC | __WASI_RIGHTS_FD_WRITE |
                    __WASI_RIGHTS_FD_ALLOCATE |
                    __WASI_RIGHTS_FD_FILESTAT_SET_SIZE;
            break;
        case O_EXEC:
            break;
        // case O_SEARCH:
        //   break;
        default:
            errno = EINVAL;
            return -1;
    }

    // Ensure that we can actually obtain the minimal rights needed.
    __wasi_fdstat_t fsb_cur;
    __wasi_errno_t error = __wasi_fd_fdstat_get(fd, &fsb_cur);
    if (error != 0)
    {
        errno = error;
        return -1;
    }

    // Path lookup properties.
    __wasi_lookupflags_t lookup_flags = 0;
    if ((flags & O_NOFOLLOW) == 0)
    {
        lookup_flags |= __WASI_LOOKUPFLAGS_SYMLINK_FOLLOW;
    }

    // Open file with appropriate rights.
    __wasi_fdflags_t fs_flags = 0;
    if ((flags & O_APPEND) != 0)
    {
        fs_flags |= __WASI_FDFLAGS_APPEND;
    }
    if ((flags & O_DSYNC) != 0)
    {
        fs_flags |= __WASI_FDFLAGS_DSYNC;
    }
    if ((flags & O_NONBLOCK) != 0)
    {
        fs_flags |= __WASI_FDFLAGS_NONBLOCK;
    }
    if ((flags & O_RSYNC) != 0)
    {
        fs_flags |= __WASI_FDFLAGS_RSYNC;
    }
    if ((flags & O_SYNC) != 0)
    {
        fs_flags |= __WASI_FDFLAGS_SYNC;
    }
    __wasi_oflags_t o_flags = 0;
    if((flags & O_CREAT) != 0)
    {
        o_flags |= __WASI_OFLAGS_CREAT;
    }
    if((flags & O_DIRECTORY) != 0)
    {
        o_flags |= __WASI_OFLAGS_DIRECTORY;
    }
    if((flags & O_EXCL) != 0)
    {
        o_flags |= __WASI_OFLAGS_EXCL;
    }
    if((flags & O_TRUNC) != 0)
    {
        o_flags |= __WASI_OFLAGS_TRUNC;
    }
    __wasi_rights_t fs_rights_base = max & fsb_cur.fs_rights_inheriting;
    __wasi_rights_t fs_rights_inheriting = fsb_cur.fs_rights_inheriting;
    __wasi_fd_t newfd;
    error = __wasi_path_open(fd, lookup_flags, path, strlen(path), o_flags,
                             fs_rights_base, fs_rights_inheriting, fs_flags,
                             &newfd);
    if (error != 0)
    {
        errno = errno_fixup_directory(fd, error);
        return -1;
    }

    return newfd;
}

int __syscall_ioctl(int fd, int op, ...) {
  return -ENOSYS;
}

long __syscall_fcntl64(long fd, long cmd, ...) {
  return -ENOSYS;
}

// Emscripten additions

extern void emscripten_notify_memory_growth(size_t memory_index);

// Should never be called in standalone mode
void *emscripten_memcpy_big(void *restrict dest, const void *restrict src, size_t n) {
  __builtin_unreachable();
}

size_t emscripten_get_heap_max() {
  // In standalone mode we don't have any wasm instructions to access the max
  // memory size so the best we can do (without calling an import) is return
  // the current heap size.
  return emscripten_get_heap_size();
}

int emscripten_resize_heap(size_t size) {
#ifdef EMSCRIPTEN_MEMORY_GROWTH
  size_t old_size = __builtin_wasm_memory_size(0) * WASM_PAGE_SIZE;
  assert(old_size < size);
  ssize_t diff = (size - old_size + WASM_PAGE_SIZE - 1) / WASM_PAGE_SIZE;
  size_t result = __builtin_wasm_memory_grow(0, diff);
  if (result != (size_t)-1) {
    // Success, update JS (see https://github.com/WebAssembly/WASI/issues/82)
    emscripten_notify_memory_growth(0);
    return 1;
  }
#endif
  return 0;
}

double emscripten_get_now(void) {
  return (1000 * clock()) / (double)CLOCKS_PER_SEC;
}

// C++ ABI

// Emscripten disables exception catching by default, but not throwing. That
// allows users to see a clear error if a throw happens, and 99% of the
// overhead is in the catching, so this is a reasonable tradeoff.
// For now, in a standalone build just terminate. TODO nice error message
//
// Define these symbols as weak so that when we build with exceptions
// enabled (using wasm-eh) we get the real versions of these functions
// as defined in libc++abi.

__attribute__((__weak__))
void __cxa_throw(void* ptr, void* type, void* destructor) {
  abort();
}

__attribute__((__weak__))
void* __cxa_allocate_exception(size_t thrown_size) {
  abort();
}

// WasmFS integration. We stub out file preloading and such, that are not
// expected to work anyhow.

size_t _wasmfs_get_num_preloaded_files() { return 0; }

size_t _wasmfs_get_num_preloaded_dirs() { return 0; }

int _wasmfs_get_preloaded_file_size(int index) { return 0; }

int _wasmfs_get_preloaded_file_mode(int index) { return 0; }

size_t _wasmfs_copy_preloaded_file_data(int index, void* buffer) { return 0; }

void _wasmfs_get_preloaded_parent_path(int index, void* buffer) {}

void _wasmfs_get_preloaded_child_path(int index, void* buffer) {}

void _wasmfs_get_preloaded_path_name(int index, void* buffer) {}

// Import the VM's fd_write under a different name. Then we can interpose in
// between it and WasmFS's fd_write. That is, libc calls fd_write, which WasmFS
// implements. And WasmFS will forward actual writing to stdout/stderr to the
// VM's fd_write. (This allows WasmFS to do work in the middle, for example, it
// could support embedded files and other functionality.)
__attribute__((import_module("wasi_snapshot_preview1"),
               import_name("fd_write"))) __wasi_errno_t
imported__wasi_fd_write(__wasi_fd_t fd,
                        const __wasi_ciovec_t* iovs,
                        size_t iovs_len,
                        __wasi_size_t* nwritten);

// Write a buffer + a newline.
static void wasi_writeln(__wasi_fd_t fd, char* buffer) {
  struct __wasi_ciovec_t iovs[2];
  iovs[0].buf = (uint8_t*)buffer;
  iovs[0].buf_len = strlen(buffer);
  iovs[1].buf = (uint8_t*)"\n";
  iovs[1].buf_len = 1;
  __wasi_size_t nwritten;
  imported__wasi_fd_write(fd, iovs, 2, &nwritten);
}

void _emscripten_out(char* text) { wasi_writeln(1, text); }

void _emscripten_err(char* text) { wasi_writeln(2, text); }
