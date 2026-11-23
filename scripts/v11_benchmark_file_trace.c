/* Opt-in libc file-open observation for the forensic runs. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdarg.h>

static void record(const char *operation, const char *path) {
    const char *log = getenv("DNK_FILE_AUDIT_LOG");
    if (log == NULL) return;
    int fd = (int)syscall(SYS_openat, AT_FDCWD, log, O_WRONLY | O_APPEND | O_CREAT, 0600);
    if (fd < 0) return;
    dprintf(fd, "%ld\t%ld\t%s\t%s\n", (long)getpid(), (long)getppid(), operation, path);
    close(fd);
}

__attribute__((constructor)) static void start(void) {
    char executable[4096];
    ssize_t length = readlink("/proc/self/exe", executable, sizeof executable - 1);
    if (length < 0) return;
    executable[length] = '\0';
    record("process_start", executable);
}

FILE *fopen(const char *path, const char *mode) {
    FILE *(*actual)(const char *, const char *) = dlsym(RTLD_NEXT, "fopen");
    record("fopen", path);
    return actual(path, mode);
}

int open(const char *path, int flags, ...) {
    int (*actual)(const char *, int, ...) = dlsym(RTLD_NEXT, "open");
    record("open", path);
    if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) {
        va_list args;
        va_start(args, flags);
        mode_t mode = va_arg(args, mode_t);
        va_end(args);
        return actual(path, flags, mode);
    }
    return actual(path, flags);
}
