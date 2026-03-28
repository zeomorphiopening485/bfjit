#define _GNU_SOURCE

#include "bfjit_internal.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#if defined(__APPLE__)
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif

#if !defined(__x86_64__) && !defined(__aarch64__)
size_t bf_jit_arch_code_size(const bf_program *program) {
    (void)program;
    return 0;
}

bool bf_jit_arch_emit_program(uint8_t *code, size_t code_size,
                              const bf_program *program, bf_jit_err *err,
                              size_t *emitted_size) {
    (void)code;
    (void)code_size;
    (void)program;
    (void)emitted_size;
    bf_set_jit_err(err,
                   "native JIT backend is unsupported on this architecture");
    return false;
}
#endif

static void bf_jit_flush_instruction_cache(void *code, size_t code_size) {
#if defined(__APPLE__)
    sys_icache_invalidate(code, code_size);
#else
    __builtin___clear_cache((char *)code, (char *)code + code_size);
#endif
}

static void bf_jit_write_protect_toggle(int enable_exec) {
#if defined(__APPLE__) && defined(__aarch64__)
    pthread_jit_write_protect_np(enable_exec != 0);
#else
    (void)enable_exec;
#endif
}

static size_t bf_jit_backend_page_align(size_t value) {
    long page_size;
    size_t page_mask;

    page_size = sysconf(_SC_PAGESIZE);
    if (page_size <= 0) {
        return 0;
    }

    page_mask = (size_t)page_size - 1;
    return (value + page_mask) & ~page_mask;
}

bool bf_jit_backend_compile(const bf_program *program,
                            bf_jit_compiled_program *compiled,
                            bf_jit_err *err) {
    size_t code_size;
    size_t emitted_size;
    size_t mapping_size;
    int mmap_flags;
    void *mapping;

    if (compiled == NULL || program == NULL) {
        bf_set_jit_err(err, "program and compiled output must be non-null");
        return false;
    }

    memset(compiled, 0, sizeof(*compiled));

    code_size = bf_jit_arch_code_size(program);
    if (code_size == 0) {
        bf_set_jit_err(
            err, "native JIT backend is unsupported on this architecture");
        return false;
    }

    mapping_size = bf_jit_backend_page_align(code_size);
    if (mapping_size == 0) {
        bf_set_jit_err(err, "failed to determine executable page size");
        return false;
    }

    mmap_flags = MAP_PRIVATE | MAP_ANON;
#if defined(__APPLE__)
#ifdef MAP_JIT
    mmap_flags |= MAP_JIT;
#endif
#endif

    mapping = mmap(NULL, mapping_size, PROT_READ | PROT_WRITE | PROT_EXEC,
                   mmap_flags, -1, 0);
    if (mapping == MAP_FAILED) {
        bf_set_jit_err(err,
                       "failed to allocate executable memory for native JIT");
        return false;
    }

    bf_jit_write_protect_toggle(0);
    if (!bf_jit_arch_emit_program((uint8_t *)mapping, code_size, program, err,
                                  &emitted_size)) {
        bf_jit_write_protect_toggle(1);
        munmap(mapping, mapping_size);
        return false;
    }
    bf_jit_flush_instruction_cache(mapping, emitted_size);
    bf_jit_write_protect_toggle(1);

    compiled->entry = (bf_jit_entry_fn)mapping;
    compiled->code = mapping;
    compiled->code_size = emitted_size;
    compiled->mapping_size = mapping_size;
    return true;
}

void bf_jit_backend_dispose(bf_jit_compiled_program *compiled) {
    if (compiled == NULL) {
        return;
    }

    if (compiled->code != NULL && compiled->mapping_size != 0) {
        munmap(compiled->code, compiled->mapping_size);
    }

    compiled->entry = NULL;
    compiled->code = NULL;
    compiled->code_size = 0;
    compiled->mapping_size = 0;
}
