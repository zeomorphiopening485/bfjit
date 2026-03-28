#if defined(__x86_64__)

#define _GNU_SOURCE

#include "bfjit_internal.h"

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct bf_jit_emitter {
    uint8_t *code;
    size_t capacity;
    size_t length;
    bf_jit_err *err;
    int guard_valid;
    int guard_min_offset;
    int guard_max_offset;
    int tape_ptr_state_valid;
    int scoped_guard_active;
    int scoped_guard_min_offset;
    int scoped_guard_max_offset;
    struct {
        int active;
        int min_offset;
        int max_offset;
    } guard_scope_stack[8192];
    size_t guard_scope_depth;
    bf_jit_label epilogue;
    bf_jit_label negative_return;
    bf_jit_label error_labels[10];
} bf_jit_emitter;

static void bf_jit_invalidate_cached_state(bf_jit_emitter *emitter) {
    emitter->guard_valid = 0;
    emitter->guard_min_offset = 0;
    emitter->guard_max_offset = 0;
    emitter->tape_ptr_state_valid = 0;
}

static void bf_jit_note_guard_window(bf_jit_emitter *emitter, int min_offset,
                                     int max_offset) {
    (void)emitter;
    (void)min_offset;
    (void)max_offset;
}

static int bf_jit_emit_ptr_range_guard(bf_jit_emitter *emitter, int min_offset,
                                       int max_offset, int min_err,
                                       int max_err);

static int bf_jit_scoped_guard_covers(const bf_jit_emitter *emitter,
                                      int min_offset, int max_offset) {
    return emitter->scoped_guard_active &&
           emitter->scoped_guard_min_offset <= min_offset &&
           emitter->scoped_guard_max_offset >= max_offset;
}

static int bf_jit_enter_guard_scope(bf_jit_emitter *emitter, int min_offset,
                                    int max_offset, int min_err, int max_err) {
    if (emitter->guard_scope_depth >=
        sizeof(emitter->guard_scope_stack) /
            sizeof(emitter->guard_scope_stack[0])) {
        bf_set_jit_err(emitter->err, "guard scope stack overflow");
        return 0;
    }

    emitter->guard_scope_stack[emitter->guard_scope_depth].active =
        emitter->scoped_guard_active;
    emitter->guard_scope_stack[emitter->guard_scope_depth].min_offset =
        emitter->scoped_guard_min_offset;
    emitter->guard_scope_stack[emitter->guard_scope_depth].max_offset =
        emitter->scoped_guard_max_offset;
    emitter->guard_scope_depth += 1;

    if (bf_jit_scoped_guard_covers(emitter, min_offset, max_offset)) {
        return 1;
    }

    if (!bf_jit_emit_ptr_range_guard(emitter, min_offset, max_offset, min_err,
                                     max_err)) {
        emitter->guard_scope_depth -= 1;
        emitter->scoped_guard_active =
            emitter->guard_scope_stack[emitter->guard_scope_depth].active;
        emitter->scoped_guard_min_offset =
            emitter->guard_scope_stack[emitter->guard_scope_depth].min_offset;
        emitter->scoped_guard_max_offset =
            emitter->guard_scope_stack[emitter->guard_scope_depth].max_offset;
        return 0;
    }

    emitter->scoped_guard_active = 1;
    emitter->scoped_guard_min_offset = min_offset;
    emitter->scoped_guard_max_offset = max_offset;
    return 1;
}

static void bf_jit_leave_guard_scope(bf_jit_emitter *emitter) {
    if (emitter->guard_scope_depth == 0) {
        return;
    }

    emitter->guard_scope_depth -= 1;
    emitter->scoped_guard_active =
        emitter->guard_scope_stack[emitter->guard_scope_depth].active;
    emitter->scoped_guard_min_offset =
        emitter->guard_scope_stack[emitter->guard_scope_depth].min_offset;
    emitter->scoped_guard_max_offset =
        emitter->guard_scope_stack[emitter->guard_scope_depth].max_offset;
}

static void bf_jit_label_init(bf_jit_label *label) {
    label->position = (size_t)-1;
    label->patches = NULL;
    label->patch_count = 0;
    label->patch_capacity = 0;
}

static void bf_jit_label_dispose(bf_jit_label *label) {
    free(label->patches);
    label->patches = NULL;
    label->patch_count = 0;
    label->patch_capacity = 0;
}

static int bf_jit_label_add_patch(bf_jit_label *label, size_t patch_offset) {
    size_t new_capacity;
    bf_jit_patch *new_patches;

    if (label->patch_count < label->patch_capacity) {
        label->patches[label->patch_count].offset = patch_offset;
        label->patches[label->patch_count].kind = BF_JIT_PATCH_BRANCH;
        label->patch_count += 1;
        return 1;
    }

    new_capacity = label->patch_capacity == 0 ? 8 : label->patch_capacity * 2;
    new_patches = realloc(label->patches, new_capacity * sizeof(*new_patches));
    if (new_patches == NULL) {
        return 0;
    }

    label->patches = new_patches;
    label->patch_capacity = new_capacity;
    label->patches[label->patch_count].offset = patch_offset;
    label->patches[label->patch_count].kind = BF_JIT_PATCH_BRANCH;
    label->patch_count += 1;
    return 1;
}

static void bf_jit_emitter_init(bf_jit_emitter *emitter, uint8_t *code,
                                size_t capacity, bf_jit_err *err) {
    size_t index;

    emitter->code = code;
    emitter->capacity = capacity;
    emitter->length = 0;
    emitter->err = err;
    bf_jit_invalidate_cached_state(emitter);
    bf_jit_label_init(&emitter->epilogue);
    bf_jit_label_init(&emitter->negative_return);
    for (index = 0; index < 10; ++index) {
        bf_jit_label_init(&emitter->error_labels[index]);
    }
}

static void bf_jit_emitter_dispose(bf_jit_emitter *emitter) {
    size_t index;

    bf_jit_label_dispose(&emitter->epilogue);
    bf_jit_label_dispose(&emitter->negative_return);
    for (index = 0; index < 10; ++index) {
        bf_jit_label_dispose(&emitter->error_labels[index]);
    }
}

static int bf_jit_emit_bytes(bf_jit_emitter *emitter, const uint8_t *bytes,
                             size_t count) {
    if (emitter->length + count > emitter->capacity) {
        bf_set_jit_err(emitter->err, "native code buffer overflow");
        return 0;
    }

    memcpy(emitter->code + emitter->length, bytes, count);
    emitter->length += count;
    return 1;
}

static int bf_jit_emit_u8(bf_jit_emitter *emitter, uint8_t value) {
    return bf_jit_emit_bytes(emitter, &value, 1);
}

static int bf_jit_emit_u32(bf_jit_emitter *emitter, uint32_t value) {
    uint8_t bytes[4];

    bytes[0] = (uint8_t)(value & 0xffu);
    bytes[1] = (uint8_t)((value >> 8) & 0xffu);
    bytes[2] = (uint8_t)((value >> 16) & 0xffu);
    bytes[3] = (uint8_t)((value >> 24) & 0xffu);
    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_u64(bf_jit_emitter *emitter, uint64_t value) {
    uint8_t bytes[8];
    size_t index;

    for (index = 0; index < sizeof(bytes); ++index) {
        bytes[index] = (uint8_t)((value >> (index * 8)) & 0xffu);
    }

    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_store_const_disp32(bf_jit_emitter *emitter, int offset,
                                          uint8_t value);
static int bf_jit_emit_add_imm8_to_disp32(bf_jit_emitter *emitter, int offset,
                                          uint8_t value);
static int bf_jit_emit_ptr_range_guard(bf_jit_emitter *emitter, int min_offset,
                                       int max_offset, int min_err,
                                       int max_err);
static int bf_jit_emit_current_cell_cmp_zero(bf_jit_emitter *emitter);
static int bf_jit_emit_op_multiply_loop_with_offset(bf_jit_emitter *emitter,
                                                    const bf_ir_node *node,
                                                    int pending_offset);
static int bf_jit_emit_simple_run_with_loaded_ptr(bf_jit_emitter *emitter,
                                                  const bf_ir_block *block,
                                                  size_t start_index,
                                                  size_t *next_index,
                                                  int *pending_offset);
static int bf_jit_emit_simple_run(bf_jit_emitter *emitter,
                                  const bf_ir_block *block, size_t start_index,
                                  size_t *next_index, int *pending_offset);
static int bf_jit_emit_block(bf_jit_emitter *emitter, const bf_ir_block *block);
static int bf_jit_emit_block_with_pending_offset(bf_jit_emitter *emitter,
                                                 const bf_ir_block *block,
                                                 int *pending_offset,
                                                 int flush_pending_offset);

static int bf_jit_patch_rel32(bf_jit_emitter *emitter, size_t patch_offset,
                              size_t target_offset) {
    int64_t delta;
    int32_t rel32;

    delta = (int64_t)target_offset - (int64_t)(patch_offset + 4);
    rel32 = (int32_t)delta;
    memcpy(emitter->code + patch_offset, &rel32, sizeof(rel32));
    return 1;
}

static int bf_jit_bind_label(bf_jit_emitter *emitter, bf_jit_label *label) {
    size_t index;

    label->position = emitter->length;
    for (index = 0; index < label->patch_count; ++index) {
        if (!bf_jit_patch_rel32(emitter, label->patches[index].offset,
                                label->position)) {
            return 0;
        }
    }

    return 1;
}

static int bf_jit_emit_label_ref(bf_jit_emitter *emitter, bf_jit_label *label) {
    size_t patch_offset;

    patch_offset = emitter->length;
    if (!bf_jit_emit_u32(emitter, 0)) {
        return 0;
    }

    if (label->position != (size_t)-1) {
        return bf_jit_patch_rel32(emitter, patch_offset, label->position);
    }

    if (!bf_jit_label_add_patch(label, patch_offset)) {
        bf_set_jit_err(emitter->err, "failed to allocate label patch");
        return 0;
    }

    return 1;
}

static int bf_jit_emit_movabs_rax(bf_jit_emitter *emitter, uint64_t value) {
    static const uint8_t opcode[] = {0x48, 0xB8};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u64(emitter, value);
}

static int bf_jit_emit_movabs_rsi(bf_jit_emitter *emitter, uint64_t value) {
    static const uint8_t opcode[] = {0x48, 0xBE};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u64(emitter, value);
}

static int bf_jit_emit_call_abs(bf_jit_emitter *emitter, uintptr_t target) {
    static const uint8_t call_rax[] = {0xFF, 0xD0};

    return bf_jit_emit_movabs_rax(emitter, (uint64_t)target) &&
           bf_jit_emit_bytes(emitter, call_rax, sizeof(call_rax));
}

static int bf_jit_emit_jmp_label(bf_jit_emitter *emitter, bf_jit_label *label) {
    return bf_jit_emit_u8(emitter, 0xE9) &&
           bf_jit_emit_label_ref(emitter, label);
}

static int bf_jit_emit_je_label(bf_jit_emitter *emitter, bf_jit_label *label) {
    static const uint8_t opcode[] = {0x0F, 0x84};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_label_ref(emitter, label);
}

static int bf_jit_emit_jne_label(bf_jit_emitter *emitter, bf_jit_label *label) {
    static const uint8_t opcode[] = {0x0F, 0x85};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_label_ref(emitter, label);
}

static int bf_jit_emit_jae_label(bf_jit_emitter *emitter, bf_jit_label *label) {
    static const uint8_t opcode[] = {0x0F, 0x83};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_label_ref(emitter, label);
}

static int bf_jit_emit_jb_label(bf_jit_emitter *emitter, bf_jit_label *label) {
    static const uint8_t opcode[] = {0x0F, 0x82};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_label_ref(emitter, label);
}

static int bf_jit_emit_js_label(bf_jit_emitter *emitter, bf_jit_label *label) {
    static const uint8_t opcode[] = {0x0F, 0x88};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_label_ref(emitter, label);
}

static int bf_jit_emit_prologue(bf_jit_emitter *emitter) {
    static const uint8_t bytes[] = {0x53, 0x48, 0x83, 0xEC, 0x20, 0x48, 0x89,
                                    0x3C, 0x24, 0x48, 0x89, 0x74, 0x24, 0x08,
                                    0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00,
                                    0x00, 0x00, 0x48, 0x89, 0xE3};

    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_epilogue_body(bf_jit_emitter *emitter, int load_result) {
    if (load_result) {
        static const uint8_t load_result_bytes[] = {0x48, 0x8B, 0x43, 0x10};

        if (!bf_jit_emit_bytes(emitter, load_result_bytes,
                               sizeof(load_result_bytes))) {
            return 0;
        }
    }

    {
        static const uint8_t bytes[] = {0x48, 0x83, 0xC4, 0x20, 0x5B, 0xC3};
        return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
    }
}

static int bf_jit_emit_current_cell_cmp_zero(bf_jit_emitter *emitter) {
    static const uint8_t bytes[] = {0x48, 0x8B, 0x03, 0x48, 0x8B, 0x4B,
                                    0x10, 0x80, 0x3C, 0x08, 0x00};

    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_op_add_ptr(bf_jit_emitter *emitter, int delta) {
    static const uint8_t load_ptr[] = {0x48, 0x8B, 0x43, 0x10};
    static const uint8_t cmp_size[] = {0x48, 0x3B, 0x43, 0x08};
    static const uint8_t store_ptr[] = {0x48, 0x89, 0x43, 0x10};

    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_bytes(emitter, load_ptr, sizeof(load_ptr)) &&
           bf_jit_emit_u8(emitter, 0x48) && bf_jit_emit_u8(emitter, 0x05) &&
           bf_jit_emit_u32(emitter, (uint32_t)delta) &&
           bf_jit_emit_bytes(emitter, cmp_size, sizeof(cmp_size)) &&
           bf_jit_emit_jae_label(emitter, &emitter->error_labels[1]) &&
           bf_jit_emit_bytes(emitter, store_ptr, sizeof(store_ptr));
}

static int bf_jit_emit_op_add_data(bf_jit_emitter *emitter, int delta) {
    static const uint8_t bytes[] = {0x48, 0x8B, 0x03, 0x48, 0x8B,
                                    0x4B, 0x10, 0x80, 0x04, 0x08};

    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes)) &&
           bf_jit_emit_u8(emitter, (uint8_t)delta);
}

static int bf_jit_emit_op_store_const(bf_jit_emitter *emitter, uint8_t value) {
    static const uint8_t bytes[] = {0x48, 0x8B, 0x03, 0x48, 0x8B,
                                    0x4B, 0x10, 0xC6, 0x04, 0x08};

    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes)) &&
           bf_jit_emit_u8(emitter, value);
}

static int bf_jit_emit_load_tape_ptr_state(bf_jit_emitter *emitter) {
    static const uint8_t bytes[] = {0x48, 0x8B, 0x03, 0x48, 0x8B, 0x4B, 0x10};

    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_add_data_with_loaded_ptr(bf_jit_emitter *emitter,
                                                int offset, int delta) {
    return bf_jit_emit_add_imm8_to_disp32(emitter, offset, (uint8_t)delta);
}

static int bf_jit_emit_store_const_with_loaded_ptr(bf_jit_emitter *emitter,
                                                   int offset, uint8_t value) {
    return bf_jit_emit_store_const_disp32(emitter, offset, value);
}

static int bf_jit_emit_op_add_data_at_offset(bf_jit_emitter *emitter,
                                             int offset, int delta) {
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 8, 9) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_add_data_with_loaded_ptr(emitter, offset, delta);
}

static int bf_jit_emit_op_store_const_at_offset(bf_jit_emitter *emitter,
                                                int offset, uint8_t value) {
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 8, 9) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_store_const_with_loaded_ptr(emitter, offset, value);
}

static int bf_jit_emit_add_rcx_imm32(bf_jit_emitter *emitter, int delta) {
    static const uint8_t opcode[] = {0x48, 0x81, 0xC1};

    if (delta == 0) {
        return 1;
    }

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)delta);
}

static int bf_jit_emit_cmp_rax_imm32(bf_jit_emitter *emitter, uint32_t value) {
    static const uint8_t opcode[] = {0x48, 0x3D};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, value);
}

static int bf_jit_emit_cmp_rcx_imm32(bf_jit_emitter *emitter, uint32_t value) {
    static const uint8_t opcode[] = {0x48, 0x81, 0xF9};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, value);
}

static int bf_jit_emit_load_scan_state(bf_jit_emitter *emitter) {
    static const uint8_t bytes[] = {0x48, 0x8B, 0x33, 0x48, 0x8B, 0x4B, 0x10};

    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_store_scan_pointer(bf_jit_emitter *emitter) {
    static const uint8_t bytes[] = {0x48, 0x89, 0x4B, 0x10};

    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_scan_cell_cmp_zero(bf_jit_emitter *emitter) {
    static const uint8_t bytes[] = {0x80, 0x3C, 0x0E, 0x00};

    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_scan_cell_disp_cmp_zero(bf_jit_emitter *emitter,
                                               int offset) {
    static const uint8_t opcode[] = {0x80, 0xBC, 0x0E};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset) &&
           bf_jit_emit_u8(emitter, 0x00);
}

static int bf_jit_emit_scan_prepare_upper_bound(bf_jit_emitter *emitter) {
    (void)emitter;
    return 1;
}

static int bf_jit_emit_scan_current_oob(bf_jit_emitter *emitter) {
    static const uint8_t cmp_rcx_size[] = {0x48, 0x3B, 0x4B, 0x08};

    return bf_jit_emit_bytes(emitter, cmp_rcx_size, sizeof(cmp_rcx_size)) &&
           bf_jit_emit_jae_label(emitter, &emitter->error_labels[3]);
}

static int bf_jit_emit_scan_advance_oob(bf_jit_emitter *emitter, int delta,
                                        bf_jit_label *label) {
    static const uint8_t mov_rax_rcx[] = {0x48, 0x89, 0xC8};
    static const uint8_t cmp_rax_size[] = {0x48, 0x3B, 0x43, 0x08};

    return bf_jit_emit_bytes(emitter, mov_rax_rcx, sizeof(mov_rax_rcx)) &&
           bf_jit_emit_u8(emitter, 0x48) && bf_jit_emit_u8(emitter, 0x05) &&
           bf_jit_emit_u32(emitter, (uint32_t)delta) &&
           bf_jit_emit_bytes(emitter, cmp_rax_size, sizeof(cmp_rax_size)) &&
           bf_jit_emit_jae_label(emitter, label);
}

static int bf_jit_emit_scan_backward_oob(bf_jit_emitter *emitter, int delta) {
    return bf_jit_emit_cmp_rcx_imm32(emitter, (uint32_t)delta) &&
           bf_jit_emit_jb_label(emitter, &emitter->error_labels[3]);
}

static int bf_jit_scan_pending_offset_is_whitelisted(int step,
                                                     int pending_offset) {
    (void)pending_offset;
    return step == 9 || step == -9;
}

static int bf_jit_emit_op_scan_with_pending_offset(bf_jit_emitter *emitter,
                                                   int step,
                                                   int pending_offset) {
    bf_jit_label loop_start;
    bf_jit_label loop_done;
    int ok;
    static const uint8_t mov_rax_rcx[] = {0x48, 0x89, 0xC8};
    static const uint8_t cmp_rcx_zero[] = {0x80, 0x3C, 0x0E, 0x00};

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_label_init(&loop_start);
    bf_jit_label_init(&loop_done);

    ok = bf_jit_emit_load_scan_state(emitter);

    if (ok && pending_offset > 0) {
        ok = bf_jit_emit_bytes(emitter, mov_rax_rcx, sizeof(mov_rax_rcx)) &&
             bf_jit_emit_u8(emitter, 0x48) && bf_jit_emit_u8(emitter, 0x05) &&
             bf_jit_emit_u32(emitter, (uint32_t)pending_offset) &&
             bf_jit_emit_bytes(emitter,
                               (const uint8_t[]){0x48, 0x3B, 0x43, 0x08}, 4) &&
             bf_jit_emit_jae_label(emitter, &emitter->error_labels[1]) &&
             bf_jit_emit_bytes(emitter, (const uint8_t[]){0x48, 0x89, 0xC1}, 3);
    } else if (ok && pending_offset < 0) {
        ok = bf_jit_emit_cmp_rcx_imm32(emitter, (uint32_t)(-pending_offset)) &&
             bf_jit_emit_jb_label(emitter, &emitter->error_labels[1]) &&
             bf_jit_emit_add_rcx_imm32(emitter, pending_offset);
    }

    ok = ok && bf_jit_emit_bytes(emitter, cmp_rcx_zero, sizeof(cmp_rcx_zero)) &&
         bf_jit_emit_je_label(emitter, &loop_done) &&
         bf_jit_bind_label(emitter, &loop_start);

    if (ok && step > 0) {
        ok = bf_jit_emit_add_rcx_imm32(emitter, step) &&
             bf_jit_emit_scan_current_oob(emitter);
    } else if (ok) {
        ok = bf_jit_emit_scan_backward_oob(emitter, -step) &&
             bf_jit_emit_add_rcx_imm32(emitter, step);
    }

    ok = ok && bf_jit_emit_bytes(emitter, cmp_rcx_zero, sizeof(cmp_rcx_zero)) &&
         bf_jit_emit_jne_label(emitter, &loop_start) &&
         bf_jit_bind_label(emitter, &loop_done) &&
         bf_jit_emit_store_scan_pointer(emitter);

    bf_jit_label_dispose(&loop_start);
    bf_jit_label_dispose(&loop_done);
    return ok;
}

static int bf_jit_bind_label_cb(void *context, bf_jit_label *label) {
    return bf_jit_bind_label(context, label);
}

static int bf_jit_emit_jump_cb(void *context, bf_jit_label *label) {
    return bf_jit_emit_jmp_label(context, label);
}

static int bf_jit_emit_scan_invalid_step_cb(void *context) {
    bf_jit_emitter *emitter;

    emitter = context;
    return bf_jit_emit_jmp_label(emitter, &emitter->error_labels[3]);
}

static int bf_jit_emit_scan_load_state_cb(void *context) {
    return bf_jit_emit_load_scan_state(context);
}

static int bf_jit_emit_scan_store_pointer_cb(void *context) {
    return bf_jit_emit_store_scan_pointer(context);
}

static int bf_jit_emit_scan_prepare_upper_bound_cb(void *context) {
    return bf_jit_emit_scan_prepare_upper_bound(context);
}

static int bf_jit_emit_scan_current_zero_cb(void *context,
                                            bf_jit_label *label) {
    return bf_jit_emit_scan_cell_cmp_zero(context) &&
           bf_jit_emit_je_label(context, label);
}

static int bf_jit_emit_scan_current_nonzero_cb(void *context,
                                               bf_jit_label *label) {
    return bf_jit_emit_scan_cell_cmp_zero(context) &&
           bf_jit_emit_jne_label(context, label);
}

static int bf_jit_emit_scan_disp_zero_cb(void *context, int offset,
                                         bf_jit_label *label) {
    return bf_jit_emit_scan_cell_disp_cmp_zero(context, offset) &&
           bf_jit_emit_je_label(context, label);
}

static int bf_jit_emit_scan_current_oob_cb(void *context) {
    return bf_jit_emit_scan_current_oob(context);
}

static int bf_jit_emit_scan_advance_oob_cb(void *context, int delta,
                                           bf_jit_label *label) {
    return bf_jit_emit_scan_advance_oob(context, delta, label);
}

static int bf_jit_emit_scan_backward_oob_cb(void *context, int delta) {
    return bf_jit_emit_scan_backward_oob(context, delta);
}

static int bf_jit_emit_scan_advance_cb(void *context, int delta) {
    return bf_jit_emit_add_rcx_imm32(context, delta);
}

static int bf_jit_emit_scan_with_pending_offset_cb(void *context,
                                                   const bf_ir_node *node,
                                                   int pending_offset) {
    bf_jit_emitter *emitter;

    if (!bf_jit_scan_pending_offset_is_whitelisted(node->arg, pending_offset)) {
        return 0;
    }

    emitter = (bf_jit_emitter *)context;
    return bf_jit_emit_op_scan_with_pending_offset(emitter, node->arg,
                                                   pending_offset)
               ? 1
               : -1;
}

static const bf_jit_scan_ops bf_jit_scan_shared_ops = {
    .label_init = bf_jit_label_init,
    .label_dispose = bf_jit_label_dispose,
    .bind_label = bf_jit_bind_label_cb,
    .emit_jump = bf_jit_emit_jump_cb,
    .emit_invalid_step = bf_jit_emit_scan_invalid_step_cb,
    .emit_load_state = bf_jit_emit_scan_load_state_cb,
    .emit_store_pointer = bf_jit_emit_scan_store_pointer_cb,
    .emit_prepare_upper_bound = bf_jit_emit_scan_prepare_upper_bound_cb,
    .emit_branch_current_zero = bf_jit_emit_scan_current_zero_cb,
    .emit_branch_current_nonzero = bf_jit_emit_scan_current_nonzero_cb,
    .emit_branch_disp_zero = bf_jit_emit_scan_disp_zero_cb,
    .emit_branch_if_current_oob = bf_jit_emit_scan_current_oob_cb,
    .emit_branch_if_advance_oob = bf_jit_emit_scan_advance_oob_cb,
    .emit_branch_if_backward_oob = bf_jit_emit_scan_backward_oob_cb,
    .emit_advance = bf_jit_emit_scan_advance_cb,
};

static int bf_jit_emit_ptr_range_guard(bf_jit_emitter *emitter, int min_offset,
                                       int max_offset, int min_err,
                                       int max_err) {
    static const uint8_t load_ptr[] = {0x48, 0x8B, 0x43, 0x10};
    static const uint8_t cmp_size[] = {0x48, 0x3B, 0x43, 0x08};

    if (bf_jit_scoped_guard_covers(emitter, min_offset, max_offset)) {
        return 1;
    }

    if (min_offset < 0) {
        if (!bf_jit_emit_bytes(emitter, load_ptr, sizeof(load_ptr)) ||
            !bf_jit_emit_cmp_rax_imm32(emitter, (uint32_t)(-min_offset)) ||
            !bf_jit_emit_jb_label(emitter, &emitter->error_labels[min_err])) {
            return 0;
        }
    }

    if (max_offset > 0) {
        if (!bf_jit_emit_bytes(emitter, load_ptr, sizeof(load_ptr)) ||
            !bf_jit_emit_u8(emitter, 0x48) || !bf_jit_emit_u8(emitter, 0x05) ||
            !bf_jit_emit_u32(emitter, (uint32_t)max_offset) ||
            !bf_jit_emit_bytes(emitter, cmp_size, sizeof(cmp_size)) ||
            !bf_jit_emit_jae_label(emitter, &emitter->error_labels[max_err])) {
            return 0;
        }
    }

    bf_jit_note_guard_window(emitter, min_offset, max_offset);
    return 1;
}

static int bf_jit_emit_store_zero_disp32(bf_jit_emitter *emitter, int offset) {
    static const uint8_t opcode[] = {0xC6, 0x84, 0x08};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset) &&
           bf_jit_emit_u8(emitter, 0x00);
}

static int bf_jit_emit_store_dl_current_cell(bf_jit_emitter *emitter) {
    static const uint8_t opcode[] = {0x88, 0x14, 0x08};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode));
}

static int bf_jit_emit_store_dl_disp32(bf_jit_emitter *emitter, int offset) {
    static const uint8_t opcode[] = {0x88, 0x94, 0x08};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset);
}

static int bf_jit_emit_store_const_disp32(bf_jit_emitter *emitter, int offset,
                                          uint8_t value) {
    static const uint8_t opcode[] = {0xC6, 0x84, 0x08};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset) &&
           bf_jit_emit_u8(emitter, value);
}

static int bf_jit_emit_store_zero_rsi_rcx_disp32(bf_jit_emitter *emitter,
                                                 int offset) {
    static const uint8_t opcode[] = {0xC6, 0x84, 0x0E};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset) &&
           bf_jit_emit_u8(emitter, 0x00);
}

static int bf_jit_emit_add_al_to_disp32(bf_jit_emitter *emitter, int offset) {
    static const uint8_t opcode[] = {0x00, 0x84, 0x0E};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset);
}

static int bf_jit_emit_add_dl_to_disp32(bf_jit_emitter *emitter, int offset) {
    static const uint8_t opcode[] = {0x00, 0x94, 0x0E};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset);
}

static int bf_jit_emit_sub_al_from_disp32(bf_jit_emitter *emitter, int offset) {
    static const uint8_t opcode[] = {0x28, 0x84, 0x0E};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset);
}

static int bf_jit_emit_sub_dl_from_disp32(bf_jit_emitter *emitter, int offset) {
    static const uint8_t opcode[] = {0x28, 0x94, 0x0E};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset);
}

static int bf_jit_emit_add_imm8_to_disp32(bf_jit_emitter *emitter, int offset,
                                          uint8_t value) {
    static const uint8_t opcode[] = {0x80, 0x84, 0x08};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset) &&
           bf_jit_emit_u8(emitter, value);
}

static int bf_jit_emit_op_input(bf_jit_emitter *emitter) {
    static const uint8_t load_base_ptr[] = {0x48, 0x8B, 0x03, 0x48,
                                            0x8B, 0x4B, 0x10};
    static const uint8_t mov_dl_al[] = {0x88, 0xC2};

    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_call_abs(emitter, (uintptr_t)bf_runtime_read_byte) &&
           bf_jit_emit_bytes(emitter, mov_dl_al, sizeof(mov_dl_al)) &&
           bf_jit_emit_bytes(emitter, load_base_ptr, sizeof(load_base_ptr)) &&
           bf_jit_emit_store_dl_current_cell(emitter);
}

static int bf_jit_emit_op_output(bf_jit_emitter *emitter) {
    static const uint8_t bytes[] = {0x48, 0x8B, 0x03, 0x48, 0x8B, 0x4B,
                                    0x10, 0x0F, 0xB6, 0x3C, 0x08};

    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes)) &&
           bf_jit_emit_call_abs(emitter, (uintptr_t)bf_runtime_write_byte);
}

static int bf_jit_emit_op_add_data_offset(bf_jit_emitter *emitter,
                                          const bf_ir_node *node) {
    return bf_jit_emit_ptr_range_guard(emitter, node->offset, node->offset, 8,
                                       9) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_add_imm8_to_disp32(emitter, node->offset,
                                          (uint8_t)node->arg);
}

static int bf_jit_emit_op_set_const_offset(bf_jit_emitter *emitter,
                                           const bf_ir_node *node) {
    return bf_jit_emit_ptr_range_guard(emitter, node->offset, node->offset, 8,
                                       9) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_store_const_disp32(emitter, node->offset,
                                          (uint8_t)node->arg);
}

static int bf_jit_emit_op_scan(bf_jit_emitter *emitter, int step) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_scan_shared(step, &bf_jit_scan_shared_ops, emitter);
}

static int bf_jit_emit_op_multi_zero(bf_jit_emitter *emitter,
                                     const bf_ir_node *node) {
    bf_jit_multi_zero_plan plan;
    size_t term_index;
    static const uint8_t load_tape_ptr[] = {0x48, 0x8B, 0x03, 0x48,
                                            0x8B, 0x4B, 0x10};
    static const uint8_t store_ptr[] = {0x48, 0x89, 0x4B, 0x10};

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_build_multi_zero_plan(node, &plan);

    if (node->term_count == 0) {
        if (plan.is_noop) {
            return 1;
        }
        return bf_jit_emit_op_add_ptr(emitter, node->arg);
    }

    if (!bf_jit_emit_ptr_range_guard(emitter, plan.min_offset, plan.max_offset,
                                     8, 9) ||
        !bf_jit_emit_bytes(emitter, load_tape_ptr, sizeof(load_tape_ptr))) {
        return 0;
    }

    for (term_index = 0; term_index < node->term_count; ++term_index) {
        if (!bf_jit_emit_store_zero_disp32(emitter,
                                           node->terms[term_index].offset)) {
            return 0;
        }
    }

    return bf_jit_emit_add_rcx_imm32(emitter, node->arg) &&
           bf_jit_emit_bytes(emitter, store_ptr, sizeof(store_ptr));
}

typedef struct bf_jit_x86_multiply_term_context {
    bf_jit_emitter *emitter;
    int base_offset;
} bf_jit_x86_multiply_term_context;

static int bf_jit_emit_load_dl_disp32(bf_jit_emitter *emitter, int offset) {
    static const uint8_t opcode[] = {0x0F, 0xB6, 0x94, 0x0E};

    return bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset);
}

static int
bf_jit_emit_multiply_term_cb(void *context,
                             const bf_jit_multiply_term_plan *term_plan) {
    static const uint8_t mov_eax_edx[] = {0x89, 0xD0};
    static const uint8_t imul_eax_imm32[] = {0x69, 0xC0};
    bf_jit_x86_multiply_term_context *term_context;
    int effective_offset;

    term_context = (bf_jit_x86_multiply_term_context *)context;
    effective_offset = term_context->base_offset + term_plan->offset;
    switch (term_plan->kind) {
    case BF_JIT_MULTIPLY_TERM_PLAN_ADD_SOURCE:
        return bf_jit_emit_add_dl_to_disp32(term_context->emitter,
                                            effective_offset);
    case BF_JIT_MULTIPLY_TERM_PLAN_SUB_SOURCE:
        return bf_jit_emit_sub_dl_from_disp32(term_context->emitter,
                                              effective_offset);
    case BF_JIT_MULTIPLY_TERM_PLAN_GENERAL:
        return bf_jit_emit_bytes(term_context->emitter, mov_eax_edx,
                                 sizeof(mov_eax_edx)) &&
               bf_jit_emit_bytes(term_context->emitter, imul_eax_imm32,
                                 sizeof(imul_eax_imm32)) &&
               bf_jit_emit_u32(term_context->emitter,
                               (uint32_t)term_plan->factor) &&
               bf_jit_emit_add_al_to_disp32(term_context->emitter,
                                            effective_offset);
    }
    return 0;
}

static int bf_jit_emit_op_multiply_loop(bf_jit_emitter *emitter,
                                        const bf_ir_node *node) {
    bf_jit_multiply_loop_plan plan;
    bf_jit_label loop_done;
    bf_jit_x86_multiply_term_context term_context;
    int ok;
    static const uint8_t load_tape_ptr[] = {0x48, 0x8B, 0x33, 0x48,
                                            0x8B, 0x4B, 0x10};
    static const uint8_t load_source[] = {0x0F, 0xB6, 0x14, 0x0E};
    static const uint8_t test_dl[] = {0x84, 0xD2};
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_build_multiply_loop_plan(node, &plan);

    if (plan.zero_current_only) {
        return bf_jit_emit_op_store_const(emitter, 0);
    }

    bf_jit_label_init(&loop_done);

    ok = bf_jit_emit_bytes(emitter, load_tape_ptr, sizeof(load_tape_ptr)) &&
         bf_jit_emit_bytes(emitter, load_source, sizeof(load_source)) &&
         bf_jit_emit_bytes(emitter, test_dl, sizeof(test_dl)) &&
         bf_jit_emit_je_label(emitter, &loop_done) &&
         bf_jit_emit_ptr_range_guard(emitter, plan.min_offset, plan.max_offset,
                                     4, 5);

    if (ok) {
        term_context.emitter = emitter;
        term_context.base_offset = 0;
        ok = bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context);
    }

    ok = ok && bf_jit_emit_store_zero_rsi_rcx_disp32(emitter, 0) &&
         bf_jit_bind_label(emitter, &loop_done);

    bf_jit_label_dispose(&loop_done);
    return ok;
}

static int bf_jit_emit_op_nonnull_multiply_loop(bf_jit_emitter *emitter,
                                                const bf_ir_node *node) {
    bf_jit_multiply_loop_plan plan;
    bf_jit_x86_multiply_term_context term_context;
    int ok;
    static const uint8_t load_tape_ptr[] = {0x48, 0x8B, 0x33, 0x48,
                                            0x8B, 0x4B, 0x10};
    static const uint8_t load_source[] = {0x0F, 0xB6, 0x14, 0x0E};
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_build_multiply_loop_plan(node, &plan);

    if (plan.zero_current_only) {
        return bf_jit_emit_op_store_const(emitter, 0);
    }

    ok = bf_jit_emit_ptr_range_guard(emitter, plan.min_offset, plan.max_offset,
                                     4, 5) &&
         bf_jit_emit_bytes(emitter, load_tape_ptr, sizeof(load_tape_ptr)) &&
         bf_jit_emit_bytes(emitter, load_source, sizeof(load_source));

    if (ok) {
        term_context.emitter = emitter;
        term_context.base_offset = 0;
        ok = bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context);
    }

    return ok && bf_jit_emit_store_zero_rsi_rcx_disp32(emitter, 0);
}

static int bf_jit_emit_op_multiply_loop_with_offset(bf_jit_emitter *emitter,
                                                    const bf_ir_node *node,
                                                    int pending_offset) {
    bf_jit_multiply_loop_plan plan;
    bf_jit_x86_multiply_term_context term_context;
    bf_jit_label loop_done;
    int combined_min;
    int combined_max;
    int ok;
    static const uint8_t load_tape_ptr[] = {0x48, 0x8B, 0x33, 0x48,
                                            0x8B, 0x4B, 0x10};
    static const uint8_t load_source[] = {0x0F, 0xB6, 0x14, 0x0E};
    static const uint8_t test_dl[] = {0x84, 0xD2};
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_build_multiply_loop_plan(node, &plan);

    if (plan.zero_current_only) {
        return bf_jit_emit_op_store_const_at_offset(emitter, pending_offset, 0)
                   ? 1
                   : -1;
    }

    combined_min = pending_offset + plan.min_offset;
    combined_max = pending_offset + plan.max_offset;
    if (pending_offset < combined_min) {
        combined_min = pending_offset;
    }
    if (pending_offset > combined_max) {
        combined_max = pending_offset;
    }

    if (node->kind == BF_IR_NONNULL_MULTIPLY_LOOP) {
        ok = bf_jit_emit_ptr_range_guard(emitter, combined_min, combined_max, 4,
                                         5) &&
             bf_jit_emit_bytes(emitter, load_tape_ptr, sizeof(load_tape_ptr)) &&
             bf_jit_emit_load_dl_disp32(emitter, pending_offset);

        if (ok) {
            term_context.emitter = emitter;
            term_context.base_offset = pending_offset;
            ok = bf_jit_emit_multiply_terms_shared(node, &term_ops,
                                                   &term_context);
        }

        return ok && bf_jit_emit_store_zero_rsi_rcx_disp32(emitter,
                                                           pending_offset)
                   ? 1
                   : -1;
    }

    bf_jit_label_init(&loop_done);

    ok = bf_jit_emit_ptr_range_guard(emitter, pending_offset, pending_offset, 4,
                                     5) &&
         bf_jit_emit_bytes(emitter, load_tape_ptr, sizeof(load_tape_ptr)) &&
         bf_jit_emit_load_dl_disp32(emitter, pending_offset) &&
         bf_jit_emit_bytes(emitter, test_dl, sizeof(test_dl)) &&
         bf_jit_emit_je_label(emitter, &loop_done) &&
         bf_jit_emit_ptr_range_guard(emitter, combined_min, combined_max, 4, 5);

    if (ok) {
        term_context.emitter = emitter;
        term_context.base_offset = pending_offset;
        ok = bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context);
    }

    ok = ok && bf_jit_emit_store_zero_rsi_rcx_disp32(emitter, pending_offset) &&
         bf_jit_bind_label(emitter, &loop_done);

    bf_jit_label_dispose(&loop_done);
    return ok ? 1 : -1;
}

static int
bf_jit_emit_nonnull_multiply_loop_loaded_state(bf_jit_emitter *emitter,
                                               const bf_ir_node *node) {
    bf_jit_x86_multiply_term_context term_context;
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    if (node->term_count == 0) {
        return bf_jit_emit_store_zero_rsi_rcx_disp32(emitter, 0);
    }

    term_context.emitter = emitter;
    term_context.base_offset = 0;
    return bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context) &&
           bf_jit_emit_store_zero_rsi_rcx_disp32(emitter, 0);
}

static int bf_jit_emit_nonnull_multiply_loop_loaded_state_with_offset(
    bf_jit_emitter *emitter, const bf_ir_node *node, int base_offset) {
    bf_jit_x86_multiply_term_context term_context;
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    if (node->term_count == 0) {
        return bf_jit_emit_store_zero_rsi_rcx_disp32(emitter, base_offset);
    }

    term_context.emitter = emitter;
    term_context.base_offset = base_offset;
    return bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context) &&
           bf_jit_emit_store_zero_rsi_rcx_disp32(emitter, base_offset);
}

static int bf_jit_emit_block(bf_jit_emitter *emitter, const bf_ir_block *block);

static int bf_jit_emit_current_cell_disp_cmp_zero(bf_jit_emitter *emitter,
                                                  int offset) {
    static const uint8_t opcode[] = {0x80, 0xBC, 0x08};

    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 1, 1) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_bytes(emitter, opcode, sizeof(opcode)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset) &&
           bf_jit_emit_u8(emitter, 0x00);
}

static int bf_jit_emit_op_loop_with_offset(bf_jit_emitter *emitter,
                                           const bf_ir_node *node,
                                           int pending_offset) {
    bf_jit_label loop_start;
    bf_jit_label loop_exit;
    int body_pending_offset;
    int ok;

    bf_jit_label_init(&loop_start);
    bf_jit_label_init(&loop_exit);
    body_pending_offset = pending_offset;

    bf_jit_invalidate_cached_state(emitter);
    ok = bf_jit_bind_label(emitter, &loop_start) &&
         bf_jit_emit_current_cell_disp_cmp_zero(emitter, pending_offset) &&
         bf_jit_emit_je_label(emitter, &loop_exit) &&
         bf_jit_emit_block_with_pending_offset(emitter, &node->body,
                                               &body_pending_offset, 0) &&
         body_pending_offset == pending_offset &&
         bf_jit_emit_current_cell_disp_cmp_zero(emitter, pending_offset) &&
         bf_jit_emit_jne_label(emitter, &loop_start);

    if (ok) {
        bf_jit_invalidate_cached_state(emitter);
        ok = bf_jit_bind_label(emitter, &loop_exit);
    }

    bf_jit_label_dispose(&loop_start);
    bf_jit_label_dispose(&loop_exit);
    return ok;
}

static int bf_jit_emit_op_if_with_offset(bf_jit_emitter *emitter,
                                         const bf_ir_node *node,
                                         int pending_offset) {
    bf_jit_label if_exit;
    bf_jit_simple_run_info tail_info;
    int body_pending_offset;
    int ok;

    bf_jit_label_init(&if_exit);
    body_pending_offset = pending_offset;

    bf_jit_invalidate_cached_state(emitter);
    if (bf_jit_if_has_nonnull_multiply_simple_tail(node, &tail_info)) {
        int combined_min;
        int combined_max;
        size_t next_index;

        combined_min = pending_offset;
        combined_max = pending_offset;
        if (pending_offset + tail_info.min_offset < combined_min) {
            combined_min = pending_offset + tail_info.min_offset;
        }
        if (pending_offset + tail_info.max_offset > combined_max) {
            combined_max = pending_offset + tail_info.max_offset;
        }

        {
            bf_jit_multiply_loop_plan multiply_plan;

            bf_jit_build_multiply_loop_plan(&node->body.nodes[0],
                                            &multiply_plan);
            if (pending_offset + multiply_plan.min_offset < combined_min) {
                combined_min = pending_offset + multiply_plan.min_offset;
            }
            if (pending_offset + multiply_plan.max_offset > combined_max) {
                combined_max = pending_offset + multiply_plan.max_offset;
            }
        }

        next_index = 1;
        ok = bf_jit_emit_current_cell_disp_cmp_zero(emitter, pending_offset) &&
             bf_jit_emit_je_label(emitter, &if_exit) &&
             bf_jit_emit_ptr_range_guard(emitter, combined_min, combined_max, 4,
                                         5) &&
             bf_jit_emit_load_tape_ptr_state(emitter) &&
             bf_jit_emit_load_dl_disp32(emitter, pending_offset) &&
             bf_jit_emit_nonnull_multiply_loop_loaded_state_with_offset(
                 emitter, &node->body.nodes[0], pending_offset) &&
             bf_jit_emit_simple_run_with_loaded_ptr(
                 emitter, &node->body, 1, &next_index, &body_pending_offset) &&
             next_index == node->body.count &&
             body_pending_offset == pending_offset;
    } else {
        ok = bf_jit_emit_current_cell_disp_cmp_zero(emitter, pending_offset) &&
             bf_jit_emit_je_label(emitter, &if_exit) &&
             bf_jit_emit_block_with_pending_offset(emitter, &node->body,
                                                   &body_pending_offset, 0) &&
             body_pending_offset == pending_offset;
    }

    if (ok) {
        bf_jit_invalidate_cached_state(emitter);
        ok = bf_jit_bind_label(emitter, &if_exit);
    }

    bf_jit_label_dispose(&if_exit);
    return ok;
}

static int bf_jit_emit_op_loop(bf_jit_emitter *emitter,
                               const bf_ir_node *node) {
    bf_jit_label loop_start;
    bf_jit_label loop_exit;
    int ok;

    bf_jit_label_init(&loop_start);
    bf_jit_label_init(&loop_exit);

    bf_jit_invalidate_cached_state(emitter);
    ok = bf_jit_bind_label(emitter, &loop_start) &&
         bf_jit_emit_current_cell_cmp_zero(emitter) &&
         bf_jit_emit_je_label(emitter, &loop_exit) &&
         bf_jit_emit_block(emitter, &node->body) &&
         bf_jit_emit_current_cell_cmp_zero(emitter) &&
         bf_jit_emit_jne_label(emitter, &loop_start);

    if (ok) {
        bf_jit_invalidate_cached_state(emitter);
        ok = bf_jit_bind_label(emitter, &loop_exit);
    }

    bf_jit_label_dispose(&loop_start);
    bf_jit_label_dispose(&loop_exit);
    return ok;
}

static int bf_jit_emit_op_if(bf_jit_emitter *emitter, const bf_ir_node *node) {
    bf_jit_label if_exit;
    bf_jit_simple_run_info tail_info;
    int ok;

    bf_jit_label_init(&if_exit);

    bf_jit_invalidate_cached_state(emitter);
    if (bf_jit_if_has_nonnull_multiply_simple_tail(node, &tail_info)) {
        bf_jit_multiply_loop_plan multiply_plan;
        int combined_min;
        int combined_max;

        bf_jit_build_multiply_loop_plan(&node->body.nodes[0], &multiply_plan);
        combined_min = multiply_plan.min_offset;
        combined_max = multiply_plan.max_offset;
        if (tail_info.min_offset < combined_min) {
            combined_min = tail_info.min_offset;
        }
        if (tail_info.max_offset > combined_max) {
            combined_max = tail_info.max_offset;
        }

        ok = bf_jit_emit_current_cell_cmp_zero(emitter) &&
             bf_jit_emit_je_label(emitter, &if_exit) &&
             bf_jit_emit_ptr_range_guard(emitter, combined_min, combined_max, 4,
                                         5) &&
             bf_jit_emit_load_tape_ptr_state(emitter) &&
             bf_jit_emit_bytes(emitter,
                               (const uint8_t[]){0x0F, 0xB6, 0x14, 0x0E}, 4) &&
             bf_jit_emit_nonnull_multiply_loop_loaded_state(
                 emitter, &node->body.nodes[0]) &&
             bf_jit_emit_simple_run_with_loaded_ptr(
                 emitter, &node->body, 1, &tail_info.next_index,
                 &tail_info.pending_offset_after);
    } else {
        ok = bf_jit_emit_current_cell_cmp_zero(emitter) &&
             bf_jit_emit_je_label(emitter, &if_exit) &&
             bf_jit_emit_block(emitter, &node->body);
    }

    if (ok) {
        bf_jit_invalidate_cached_state(emitter);
        ok = bf_jit_bind_label(emitter, &if_exit);
    }

    bf_jit_label_dispose(&if_exit);
    return ok;
}

static int bf_jit_emit_node(bf_jit_emitter *emitter, const bf_ir_node *node) {
    switch (node->kind) {
    case BF_IR_ADD_PTR:
        return bf_jit_emit_op_add_ptr(emitter, node->arg);
    case BF_IR_ADD_DATA:
        return bf_jit_emit_op_add_data(emitter, node->arg);
    case BF_IR_ADD_DATA_OFFSET:
        return bf_jit_emit_op_add_data_offset(emitter, node);
    case BF_IR_SET_ZERO:
        return bf_jit_emit_op_store_const(emitter, 0);
    case BF_IR_SET_CONST:
        return bf_jit_emit_op_store_const(emitter, (uint8_t)node->arg);
    case BF_IR_SET_CONST_OFFSET:
        return bf_jit_emit_op_set_const_offset(emitter, node);
    case BF_IR_INPUT:
        return bf_jit_emit_op_input(emitter);
    case BF_IR_OUTPUT:
        return bf_jit_emit_op_output(emitter);
    case BF_IR_SCAN:
        return bf_jit_emit_op_scan(emitter, node->arg);
    case BF_IR_MULTI_ZERO:
        return bf_jit_emit_op_multi_zero(emitter, node);
    case BF_IR_MULTIPLY_LOOP:
        return bf_jit_emit_op_multiply_loop(emitter, node);
    case BF_IR_NONNULL_MULTIPLY_LOOP:
        return bf_jit_emit_op_nonnull_multiply_loop(emitter, node);
    case BF_IR_LOOP:
        return bf_jit_emit_op_loop(emitter, node);
    case BF_IR_IF:
        return bf_jit_emit_op_if(emitter, node);
    default:
        bf_set_jit_err(emitter->err, "unsupported IR node for native emitter");
        return 0;
    }
}

static int bf_jit_emit_simple_node_with_offset(bf_jit_emitter *emitter,
                                               const bf_ir_node *node,
                                               int pending_offset) {
    switch (node->kind) {
    case BF_IR_ADD_DATA:
        return bf_jit_emit_op_add_data_at_offset(emitter, pending_offset,
                                                 node->arg);
    case BF_IR_SET_ZERO:
        return bf_jit_emit_op_store_const_at_offset(emitter, pending_offset, 0);
    case BF_IR_SET_CONST:
        return bf_jit_emit_op_store_const_at_offset(emitter, pending_offset,
                                                    (uint8_t)node->arg);
    case BF_IR_ADD_DATA_OFFSET:
        return bf_jit_emit_op_add_data_at_offset(
            emitter, pending_offset + node->offset, node->arg);
    case BF_IR_SET_CONST_OFFSET:
        return bf_jit_emit_op_store_const_at_offset(
            emitter, pending_offset + node->offset, (uint8_t)node->arg);
    default:
        return 0;
    }
}

static int bf_jit_emit_simple_effect(bf_jit_emitter *emitter,
                                     int effective_offset,
                                     bf_jit_simple_effect_kind effect_kind,
                                     uint8_t effect_value) {
    if (effect_kind == BF_JIT_SIMPLE_EFFECT_NONE) {
        return 1;
    }
    if (effect_kind == BF_JIT_SIMPLE_EFFECT_ADD) {
        return bf_jit_emit_add_data_with_loaded_ptr(emitter, effective_offset,
                                                    effect_value);
    }
    return bf_jit_emit_store_const_with_loaded_ptr(emitter, effective_offset,
                                                   effect_value);
}

static int bf_jit_emit_two_simple_nodes(bf_jit_emitter *emitter,
                                        const bf_ir_node *first_node,
                                        int first_pending_offset,
                                        const bf_ir_node *second_node,
                                        int second_pending_offset) {
    bf_jit_two_simple_effects effects;

    bf_jit_build_two_simple_effects(first_node, first_pending_offset,
                                    second_node, second_pending_offset,
                                    &effects);
    if (effects.count == 0) {
        return 1;
    }
    if (!bf_jit_emit_simple_effect(emitter, effects.effects[0].effective_offset,
                                   effects.effects[0].kind,
                                   effects.effects[0].value)) {
        return 0;
    }
    if (effects.count == 1) {
        return 1;
    }
    return bf_jit_emit_simple_effect(
        emitter, effects.effects[1].effective_offset, effects.effects[1].kind,
        effects.effects[1].value);
}

static int bf_jit_emit_simple_run_with_loaded_ptr(bf_jit_emitter *emitter,
                                                  const bf_ir_block *block,
                                                  size_t start_index,
                                                  size_t *next_index,
                                                  int *pending_offset) {
    bf_jit_simple_run_info info;
    size_t index;
    int scan_offset;
    int pending_effective_offset;
    bf_jit_simple_effect_kind effect_kind;
    uint8_t effect_value;

    bf_jit_collect_simple_run_info(block, start_index, *pending_offset, &info);
    *next_index = info.next_index;
    if (!info.has_simple) {
        *pending_offset = info.pending_offset_after;
        return 1;
    }

    if (info.simple_count == 1) {
        if (!bf_jit_emit_simple_effect(
                emitter,
                bf_jit_simple_node_effective_offset(
                    &block->nodes[info.first_simple_index],
                    info.first_simple_pending_offset),
                bf_jit_simple_node_effect_kind(
                    &block->nodes[info.first_simple_index]),
                bf_jit_simple_node_effect_value(
                    &block->nodes[info.first_simple_index]))) {
            return 0;
        }
        *pending_offset = info.pending_offset_after;
        return 1;
    }

    if (info.simple_count == 2) {
        if (!bf_jit_emit_two_simple_nodes(
                emitter, &block->nodes[info.first_simple_index],
                info.first_simple_pending_offset,
                &block->nodes[info.second_simple_index],
                info.second_simple_pending_offset)) {
            return 0;
        }
        *pending_offset = info.pending_offset_after;
        return 1;
    }

    scan_offset = *pending_offset;
    effect_kind = BF_JIT_SIMPLE_EFFECT_NONE;
    pending_effective_offset = 0;
    effect_value = 0;
    for (index = start_index; index < *next_index; ++index) {
        const bf_ir_node *node;
        int effective_offset;
        bf_jit_simple_effect_kind next_kind;

        node = &block->nodes[index];
        if (node->kind == BF_IR_ADD_PTR) {
            scan_offset += node->arg;
            continue;
        }
        effective_offset =
            bf_jit_simple_node_effective_offset(node, scan_offset);
        next_kind = bf_jit_simple_node_effect_kind(node);
        if (effect_kind != BF_JIT_SIMPLE_EFFECT_NONE &&
            effective_offset != pending_effective_offset) {
            if (!bf_jit_emit_simple_effect(emitter, pending_effective_offset,
                                           effect_kind, effect_value)) {
                return 0;
            }
            effect_kind = BF_JIT_SIMPLE_EFFECT_NONE;
        }
        if (effect_kind == BF_JIT_SIMPLE_EFFECT_NONE) {
            pending_effective_offset = effective_offset;
            effect_value = 0;
        }
        bf_jit_merge_simple_effect(&effect_kind, &effect_value, next_kind,
                                   bf_jit_simple_node_effect_value(node));
    }

    if (!bf_jit_emit_simple_effect(emitter, pending_effective_offset,
                                   effect_kind, effect_value)) {
        return 0;
    }

    *pending_offset = info.pending_offset_after;
    return 1;
}

static int bf_jit_emit_simple_node_batched(bf_jit_emitter *emitter,
                                           const bf_ir_node *node,
                                           int pending_offset) {
    int effective_offset;

    effective_offset =
        bf_jit_simple_node_effective_offset(node, pending_offset);
    switch (node->kind) {
    case BF_IR_ADD_DATA:
    case BF_IR_ADD_DATA_OFFSET:
        return bf_jit_emit_add_data_with_loaded_ptr(emitter, effective_offset,
                                                    node->arg);
    case BF_IR_SET_ZERO:
        return bf_jit_emit_store_const_with_loaded_ptr(emitter,
                                                       effective_offset, 0);
    case BF_IR_SET_CONST:
    case BF_IR_SET_CONST_OFFSET:
        return bf_jit_emit_store_const_with_loaded_ptr(
            emitter, effective_offset, (uint8_t)node->arg);
    default:
        return 0;
    }
}

static int bf_jit_emit_simple_run(bf_jit_emitter *emitter,
                                  const bf_ir_block *block, size_t start_index,
                                  size_t *next_index, int *pending_offset) {
    bf_jit_simple_run_info info;
    size_t index;
    int scan_offset;
    int pending_effective_offset;
    bf_jit_simple_effect_kind effect_kind;
    uint8_t effect_value;

    bf_jit_collect_simple_run_info(block, start_index, *pending_offset, &info);
    *next_index = info.next_index;
    if (!info.has_simple) {
        *pending_offset = info.pending_offset_after;
        return 1;
    }

    if (info.simple_count == 1) {
        if (!bf_jit_emit_simple_node_with_offset(
                emitter, &block->nodes[info.first_simple_index],
                info.first_simple_pending_offset)) {
            return 0;
        }
        *pending_offset = info.pending_offset_after;
        return 1;
    }

    if (!bf_jit_emit_ptr_range_guard(emitter, info.min_offset, info.max_offset,
                                     8, 9) ||
        !bf_jit_emit_load_tape_ptr_state(emitter)) {
        return 0;
    }

    if (info.simple_count == 2) {
        if (!bf_jit_emit_two_simple_nodes(
                emitter, &block->nodes[info.first_simple_index],
                info.first_simple_pending_offset,
                &block->nodes[info.second_simple_index],
                info.second_simple_pending_offset)) {
            return 0;
        }
        *pending_offset = info.pending_offset_after;
        return 1;
    }

    scan_offset = *pending_offset;
    effect_kind = BF_JIT_SIMPLE_EFFECT_NONE;
    pending_effective_offset = 0;
    effect_value = 0;
    for (index = start_index; index < *next_index; ++index) {
        const bf_ir_node *node;
        int effective_offset;
        bf_jit_simple_effect_kind next_kind;

        node = &block->nodes[index];
        if (node->kind == BF_IR_ADD_PTR) {
            scan_offset += node->arg;
            continue;
        }
        effective_offset =
            bf_jit_simple_node_effective_offset(node, scan_offset);
        next_kind = bf_jit_simple_node_effect_kind(node);
        if (effect_kind != BF_JIT_SIMPLE_EFFECT_NONE &&
            effective_offset != pending_effective_offset) {
            if (!bf_jit_emit_simple_effect(emitter, pending_effective_offset,
                                           effect_kind, effect_value)) {
                return 0;
            }
            effect_kind = BF_JIT_SIMPLE_EFFECT_NONE;
        }
        if (effect_kind == BF_JIT_SIMPLE_EFFECT_NONE) {
            pending_effective_offset = effective_offset;
            effect_value = 0;
        }
        bf_jit_merge_simple_effect(&effect_kind, &effect_value, next_kind,
                                   bf_jit_simple_node_effect_value(node));
    }

    if (!bf_jit_emit_simple_effect(emitter, pending_effective_offset,
                                   effect_kind, effect_value)) {
        return 0;
    }

    *pending_offset = info.pending_offset_after;
    return 1;
}

static int bf_jit_emit_input_at_offset(bf_jit_emitter *emitter, int offset) {
    static const uint8_t mov_dl_al[] = {0x88, 0xC2};

    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 8, 9) &&
           bf_jit_emit_call_abs(emitter, (uintptr_t)bf_runtime_read_byte) &&
           bf_jit_emit_bytes(emitter, mov_dl_al, sizeof(mov_dl_al)) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_store_dl_disp32(emitter, offset);
}

static int bf_jit_emit_output_at_offset(bf_jit_emitter *emitter, int offset) {
    static const uint8_t load_edi_disp32[] = {0x0F, 0xB6, 0xBC, 0x08};

    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 8, 9) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_bytes(emitter, load_edi_disp32,
                             sizeof(load_edi_disp32)) &&
           bf_jit_emit_u32(emitter, (uint32_t)offset) &&
           bf_jit_emit_call_abs(emitter, (uintptr_t)bf_runtime_write_byte);
}

static int bf_jit_emit_simple_run_cb(void *context, const bf_ir_block *block,
                                     size_t start_index, size_t *next_index,
                                     int *pending_offset) {
    return bf_jit_emit_simple_run((bf_jit_emitter *)context, block, start_index,
                                  next_index, pending_offset);
}

static int bf_jit_enter_guard_scope_cb(void *context, int min_offset,
                                       int max_offset, int min_err,
                                       int max_err) {
    return bf_jit_enter_guard_scope((bf_jit_emitter *)context, min_offset,
                                    max_offset, min_err, max_err);
}

static void bf_jit_leave_guard_scope_cb(void *context) {
    bf_jit_leave_guard_scope((bf_jit_emitter *)context);
}

static int bf_jit_emit_input_at_offset_cb(void *context, int offset) {
    return bf_jit_emit_input_at_offset((bf_jit_emitter *)context, offset);
}

static int bf_jit_emit_output_at_offset_cb(void *context, int offset) {
    return bf_jit_emit_output_at_offset((bf_jit_emitter *)context, offset);
}

static int bf_jit_emit_multiply_with_pending_offset_cb(void *context,
                                                       const bf_ir_node *node,
                                                       int pending_offset) {
    return bf_jit_emit_op_multiply_loop_with_offset((bf_jit_emitter *)context,
                                                    node, pending_offset);
}

static int bf_jit_emit_control_with_pending_offset_cb(void *context,
                                                      const bf_ir_node *node,
                                                      int pending_offset) {
    bf_jit_emitter *emitter;

    emitter = (bf_jit_emitter *)context;
    if (node->kind == BF_IR_LOOP) {
        return bf_jit_emit_op_loop_with_offset(emitter, node, pending_offset);
    }
    if (node->kind == BF_IR_IF) {
        return bf_jit_emit_op_if_with_offset(emitter, node, pending_offset);
    }
    return 0;
}

static int bf_jit_emit_add_ptr_cb(void *context, int delta) {
    return bf_jit_emit_op_add_ptr((bf_jit_emitter *)context, delta);
}

static int bf_jit_emit_node_cb(void *context, const bf_ir_node *node) {
    return bf_jit_emit_node((bf_jit_emitter *)context, node);
}

static int bf_jit_emit_block_with_pending_offset(bf_jit_emitter *emitter,
                                                 const bf_ir_block *block,
                                                 int *pending_offset,
                                                 int flush_pending_offset) {
    static const bf_jit_pending_offset_ops ops = {
        bf_jit_emit_simple_run_cb,
        bf_jit_emit_control_with_pending_offset_cb,
        bf_jit_emit_input_at_offset_cb,
        bf_jit_emit_output_at_offset_cb,
        bf_jit_emit_add_ptr_cb,
        bf_jit_emit_scan_with_pending_offset_cb,
        bf_jit_emit_multiply_with_pending_offset_cb,
        bf_jit_emit_node_cb,
    };

    return bf_jit_emit_block_with_pending_offset_shared(
        block, pending_offset, flush_pending_offset, &ops, emitter);
}

static int bf_jit_emit_block(bf_jit_emitter *emitter,
                             const bf_ir_block *block) {
    int pending_offset;

    pending_offset = 0;
    return bf_jit_emit_block_with_pending_offset(emitter, block,
                                                 &pending_offset, 1);
}

static int bf_jit_emit_error_block(bf_jit_emitter *emitter, int reason) {
    if (emitter->error_labels[reason].patch_count == 0) {
        return 1;
    }

    return bf_jit_bind_label(emitter, &emitter->error_labels[reason]) &&
           bf_jit_emit_u8(emitter, 0xB8) &&
           bf_jit_emit_u32(emitter, (uint32_t)(-reason)) &&
           bf_jit_emit_jmp_label(emitter, &emitter->epilogue);
}

static size_t bf_jit_node_size_hint(const bf_ir_node *node, void *context) {
    (void)context;
    switch (node->kind) {
    case BF_IR_ADD_PTR:
        return 32;
    case BF_IR_ADD_DATA:
    case BF_IR_ADD_DATA_OFFSET:
    case BF_IR_SET_ZERO:
    case BF_IR_SET_CONST:
    case BF_IR_SET_CONST_OFFSET:
        return 16;
    case BF_IR_INPUT:
    case BF_IR_OUTPUT:
        return 32;
    case BF_IR_SCAN: {
        bf_jit_scan_plan plan;

        bf_jit_build_scan_plan(node->arg, &plan);
        switch (plan.kind) {
        case BF_JIT_SCAN_PLAN_STEP1:
        case BF_JIT_SCAN_PLAN_STRIDE4:
            return 128;
        case BF_JIT_SCAN_PLAN_GENERIC:
            return 128;
        case BF_JIT_SCAN_PLAN_ERROR:
        default:
            return 128;
        }
    }
    case BF_IR_MULTI_ZERO: {
        bf_jit_multi_zero_plan plan;

        bf_jit_build_multi_zero_plan(node, &plan);
        return 48 + node->term_count * 8 +
               (!plan.is_noop && node->arg != 0 ? 8 : 0);
    }
    case BF_IR_MULTIPLY_LOOP:
    case BF_IR_NONNULL_MULTIPLY_LOOP: {
        bf_jit_multiply_loop_plan plan;

        bf_jit_build_multiply_loop_plan(node, &plan);
        return plan.zero_current_only ? 16 : 64 + node->term_count * 16;
    }
    case BF_IR_LOOP:
        return 24;
    case BF_IR_IF:
        return 16;
    default:
        return 32;
    }
}

size_t bf_jit_arch_code_size(const bf_program *program) {
    static const bf_jit_size_hint_ops ops = {
        bf_jit_node_size_hint,
        NULL,
    };
    size_t total;

    total = (256 + bf_jit_block_size_hint_shared(&program->root, &ops)) * 2;
    if (total < 16384) {
        total = 16384;
    }
    return total;
}

bool bf_jit_arch_emit_program(uint8_t *code, size_t code_size,
                              const bf_program *program, bf_jit_err *err,
                              size_t *emitted_size) {
    bf_jit_emitter emitter;
    int reason;

    bf_jit_emitter_init(&emitter, code, code_size, err);

    if (!bf_jit_emit_prologue(&emitter) ||
        !bf_jit_emit_block(&emitter, &program->root) ||
        !bf_jit_bind_label(&emitter, &emitter.epilogue) ||
        !bf_jit_emit_epilogue_body(&emitter, 1) ||
        !bf_jit_bind_label(&emitter, &emitter.negative_return) ||
        !bf_jit_emit_epilogue_body(&emitter, 0)) {
        bf_jit_emitter_dispose(&emitter);
        return false;
    }

    for (reason = 1; reason <= 9; ++reason) {
        if ((reason == 6 || reason == 7) &&
            emitter.error_labels[reason].patch_count == 0) {
            continue;
        }
        if (!bf_jit_emit_error_block(&emitter, reason)) {
            bf_jit_emitter_dispose(&emitter);
            return false;
        }
    }

    *emitted_size = emitter.length;
    bf_jit_emitter_dispose(&emitter);
    return true;
}

#else
static const int bf_jit_arch_translation_unit_anchor_x86_64
    __attribute__((used)) = 0;
#endif
