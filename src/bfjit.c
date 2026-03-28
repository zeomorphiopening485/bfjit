#define _GNU_SOURCE

#include "bfjit_internal.h"

#include <stdint.h>
#include <stdio.h>

bool bf_jit_dump_program_code(const bf_program *program,
                              const char *output_path, bf_jit_err *err) {
    bf_jit_compiled_program compiled;
    FILE *output;

    bf_jit_err_reset(err);

    if (program == NULL || output_path == NULL) {
        bf_set_jit_err(err, "program and output path must be non-null");
        return false;
    }

    if (!bf_jit_backend_compile(program, &compiled, err)) {
        return false;
    }

    output = fopen(output_path, "wb");
    if (output == NULL) {
        bf_jit_backend_dispose(&compiled);
        bf_set_jit_err(err, "failed to open JIT dump output file");
        return false;
    }

    if (compiled.code_size != 0 && fwrite(compiled.code, 1, compiled.code_size,
                                          output) != compiled.code_size) {
        fclose(output);
        bf_jit_backend_dispose(&compiled);
        bf_set_jit_err(err, "failed to write JIT dump output file");
        return false;
    }

    fclose(output);
    bf_jit_backend_dispose(&compiled);
    return true;
}

void bf_jit_err_reset(bf_jit_err *err) {
    if (err == NULL) {
        return;
    }

    err->has_err = false;
    err->msg[0] = '\0';
}

void bf_set_jit_err(bf_jit_err *err, const char *msg) {
    if (err == NULL) {
        return;
    }

    err->has_err = true;
    snprintf(err->msg, sizeof(err->msg), "%s", msg);
}

bool bf_jit_execute_program(const bf_program *program, uint8_t *tape,
                            size_t tape_size, bf_jit_err *err) {
    bf_jit_compiled_program compiled;
    int execution_result;

    bf_jit_err_reset(err);

    if (program == NULL || tape == NULL) {
        bf_set_jit_err(err, "program and tape must be non-null");
        return false;
    }

    if (!bf_jit_backend_compile(program, &compiled, err)) {
        return false;
    }

    flockfile(stdout);
    flockfile(stdin);
    execution_result = compiled.entry(tape, tape_size);
    funlockfile(stdin);
    funlockfile(stdout);

    bf_jit_backend_dispose(&compiled);

    if (execution_result < 0) {
        switch (-execution_result) {
        case 1:
            bf_set_jit_err(err, "tape pointer moved out of bounds (add_ptr)");
            break;
        case 2:
            bf_set_jit_err(err,
                           "tape pointer moved out of bounds (scan memchr)");
            break;
        case 3:
            bf_set_jit_err(err, "tape pointer moved out of bounds (scan)");
            break;
        case 4:
            bf_set_jit_err(err,
                           "tape pointer moved out of bounds (multiply min)");
            break;
        case 5:
            bf_set_jit_err(err,
                           "tape pointer moved out of bounds (multiply max)");
            break;
        case 8:
            bf_set_jit_err(err,
                           "tape pointer moved out of bounds (segment min)");
            break;
        case 9:
            bf_set_jit_err(err,
                           "tape pointer moved out of bounds (segment max)");
            break;
        default:
            bf_set_jit_err(err, "tape pointer moved out of bounds");
            break;
        }
        return false;
    }

    return true;
}
