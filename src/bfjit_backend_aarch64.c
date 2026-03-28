#if defined(__aarch64__)

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
    bf_jit_label error_labels[10];
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
} bf_jit_emitter;

static void bf_jit_invalidate_cached_state(bf_jit_emitter *emitter) {
    emitter->guard_valid = 0;
    emitter->guard_min_offset = 0;
    emitter->guard_max_offset = 0;
    emitter->tape_ptr_state_valid = 0;
}

static int bf_jit_scoped_guard_covers(const bf_jit_emitter *emitter,
                                      int min_offset, int max_offset) {
    return emitter->scoped_guard_active &&
           emitter->scoped_guard_min_offset <= min_offset &&
           emitter->scoped_guard_max_offset >= max_offset;
}

typedef struct bf_jit_guard_scope_state {
    int active;
    int min_offset;
    int max_offset;
} bf_jit_guard_scope_state;

typedef struct bf_jit_block_guard_plan {
    int valid;
    int final_delta;
    int min_offset;
    int max_offset;
} bf_jit_block_guard_plan;

static int bf_jit_emit_ptr_range_guard(bf_jit_emitter *emitter, int min_offset,
                                       int max_offset, int min_err,
                                       int max_err);

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

static void bf_jit_note_guard_window(bf_jit_emitter *emitter, int min_offset,
                                     int max_offset) {
    (void)emitter;
    (void)min_offset;
    (void)max_offset;
}

static void bf_jit_guard_plan_record_access(bf_jit_block_guard_plan *plan,
                                            int offset) {
    if (offset < plan->min_offset) {
        plan->min_offset = offset;
    }
    if (offset > plan->max_offset) {
        plan->max_offset = offset;
    }
}

static int bf_jit_build_block_guard_plan(const bf_ir_block *block,
                                         bf_jit_block_guard_plan *plan) {
    size_t index;
    int current_offset;

    plan->valid = 1;
    plan->final_delta = 0;
    plan->min_offset = 0;
    plan->max_offset = 0;
    current_offset = 0;

    for (index = 0; index < block->count; ++index) {
        const bf_ir_node *node;

        node = &block->nodes[index];
        switch (node->kind) {
        case BF_IR_ADD_PTR:
            current_offset += node->arg;
            bf_jit_guard_plan_record_access(plan, current_offset);
            break;
        case BF_IR_ADD_DATA:
        case BF_IR_SET_ZERO:
        case BF_IR_SET_CONST:
        case BF_IR_INPUT:
        case BF_IR_OUTPUT:
            bf_jit_guard_plan_record_access(plan, current_offset);
            break;
        case BF_IR_ADD_DATA_OFFSET:
        case BF_IR_SET_CONST_OFFSET:
            bf_jit_guard_plan_record_access(plan,
                                            current_offset + node->offset);
            break;
        case BF_IR_MULTI_ZERO: {
            bf_jit_multi_zero_plan node_plan;

            bf_jit_build_multi_zero_plan(node, &node_plan);
            if (!node_plan.is_noop) {
                bf_jit_guard_plan_record_access(plan, current_offset +
                                                          node_plan.min_offset);
                bf_jit_guard_plan_record_access(plan, current_offset +
                                                          node_plan.max_offset);
            }
            current_offset += node->arg;
            bf_jit_guard_plan_record_access(plan, current_offset);
            break;
        }
        case BF_IR_MULTIPLY_LOOP:
        case BF_IR_NONNULL_MULTIPLY_LOOP: {
            bf_jit_multiply_loop_plan node_plan;

            bf_jit_build_multiply_loop_plan(node, &node_plan);
            bf_jit_guard_plan_record_access(plan, current_offset);
            if (node_plan.has_terms) {
                bf_jit_guard_plan_record_access(plan, current_offset +
                                                          node_plan.min_offset);
                bf_jit_guard_plan_record_access(plan, current_offset +
                                                          node_plan.max_offset);
            }
            break;
        }
        case BF_IR_IF:
        case BF_IR_LOOP: {
            bf_jit_block_guard_plan child_plan;

            if (!bf_jit_build_block_guard_plan(&node->body, &child_plan) ||
                child_plan.final_delta != 0) {
                plan->valid = 0;
                return 0;
            }
            bf_jit_guard_plan_record_access(plan, current_offset +
                                                      child_plan.min_offset);
            bf_jit_guard_plan_record_access(plan, current_offset +
                                                      child_plan.max_offset);
            bf_jit_guard_plan_record_access(plan, current_offset);
            break;
        }
        case BF_IR_SCAN:
            plan->valid = 0;
            return 0;
        default:
            plan->valid = 0;
            return 0;
        }
    }

    plan->final_delta = current_offset;
    return 1;
}

static int
bf_jit_guard_plan_is_profitable(const bf_jit_block_guard_plan *plan) {
    return plan->valid && plan->final_delta == 0 &&
           (plan->max_offset - plan->min_offset) <= 4;
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

static int bf_jit_label_add_patch(bf_jit_label *label, size_t offset,
                                  bf_jit_patch_kind kind) {
    size_t new_capacity;
    bf_jit_patch *new_patches;

    if (label->patch_count < label->patch_capacity) {
        label->patches[label->patch_count].offset = offset;
        label->patches[label->patch_count].kind = kind;
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
    label->patches[label->patch_count].offset = offset;
    label->patches[label->patch_count].kind = kind;
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
    for (index = 0; index < 10; ++index) {
        bf_jit_label_init(&emitter->error_labels[index]);
    }
}

static void bf_jit_emitter_dispose(bf_jit_emitter *emitter) {
    size_t index;

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

static int bf_jit_emit_u32(bf_jit_emitter *emitter, uint32_t value) {
    uint8_t bytes[4];

    bytes[0] = (uint8_t)(value & 0xffu);
    bytes[1] = (uint8_t)((value >> 8) & 0xffu);
    bytes[2] = (uint8_t)((value >> 16) & 0xffu);
    bytes[3] = (uint8_t)((value >> 24) & 0xffu);
    return bf_jit_emit_bytes(emitter, bytes, sizeof(bytes));
}

static int bf_jit_emit_add_or_sub_x_imm(bf_jit_emitter *emitter, unsigned reg,
                                        int delta);
static int bf_jit_emit_op_set_zero(bf_jit_emitter *emitter);
static int bf_jit_emit_compute_target_ptr(bf_jit_emitter *emitter,
                                          unsigned dst_reg, int offset);
static int bf_jit_emit_load_tape_ptr_state(bf_jit_emitter *emitter);
static int
bf_jit_emit_load_current_cell_ptr_state_at_offset(bf_jit_emitter *emitter,
                                                  int offset);
static int bf_jit_emit_current_cell_branch_zero(bf_jit_emitter *emitter,
                                                bf_jit_label *label);
static int bf_jit_emit_op_set_const_at_offset(bf_jit_emitter *emitter,
                                              int offset, uint8_t value);
static int bf_jit_emit_op_multiply_loop_with_offset(bf_jit_emitter *emitter,
                                                    const bf_ir_node *node,
                                                    int pending_offset);
static int bf_jit_emit_set_const_with_loaded_ptr(bf_jit_emitter *emitter,
                                                 int offset, uint8_t value);
static int bf_jit_emit_simple_run(bf_jit_emitter *emitter,
                                  const bf_ir_block *block, size_t start_index,
                                  size_t *next_index, int *pending_offset);
static int bf_jit_emit_simple_run_with_loaded_ptr(bf_jit_emitter *emitter,
                                                  const bf_ir_block *block,
                                                  size_t start_index,
                                                  size_t *next_index,
                                                  int *pending_offset);
static int bf_jit_emit_simple_run_with_loaded_ptr_base_offset(
    bf_jit_emitter *emitter, const bf_ir_block *block, size_t start_index,
    size_t *next_index, int *pending_offset, int base_offset);
static int bf_jit_emit_block(bf_jit_emitter *emitter, const bf_ir_block *block);
static int bf_jit_emit_block_with_pending_offset(bf_jit_emitter *emitter,
                                                 const bf_ir_block *block,
                                                 int *pending_offset,
                                                 int flush_pending_offset);
static int bf_jit_build_block_guard_plan(const bf_ir_block *block,
                                         bf_jit_block_guard_plan *plan);

static uint32_t bf_jit_movz(unsigned reg, uint16_t imm16, unsigned shift) {
    return 0xD2800000u | ((uint32_t)(shift / 16) << 21) |
           ((uint32_t)imm16 << 5) | reg;
}

static uint32_t bf_jit_movk(unsigned reg, uint16_t imm16, unsigned shift) {
    return 0xF2800000u | ((uint32_t)(shift / 16) << 21) |
           ((uint32_t)imm16 << 5) | reg;
}

static uint32_t bf_jit_movz_w(unsigned reg, uint16_t imm16, unsigned shift) {
    return 0x52800000u | ((uint32_t)(shift / 16) << 21) |
           ((uint32_t)imm16 << 5) | reg;
}

static uint32_t bf_jit_movk_w(unsigned reg, uint16_t imm16, unsigned shift) {
    return 0x72800000u | ((uint32_t)(shift / 16) << 21) |
           ((uint32_t)imm16 << 5) | reg;
}

static uint32_t bf_jit_add_x_reg(unsigned dst, unsigned lhs, unsigned rhs) {
    return 0x8B000000u | (rhs << 16) | (lhs << 5) | dst;
}

static uint32_t bf_jit_cmp_x_reg(unsigned lhs, unsigned rhs) {
    return 0xEB00001Fu | (rhs << 16) | (lhs << 5);
}

static uint32_t bf_jit_cmp_x_imm(unsigned reg, unsigned imm12) {
    return 0xF100001Fu | ((imm12 & 0xfffu) << 10) | (reg << 5);
}

static uint32_t bf_jit_mov_x(unsigned dst, unsigned src) {
    return 0x91000000u | (src << 5) | dst;
}

static uint32_t bf_jit_ldrb_uimm(unsigned rt, unsigned rn) {
    return 0x39400000u | (rn << 5) | rt;
}

static uint32_t bf_jit_ldrb_uimm_offset(unsigned rt, unsigned rn,
                                        unsigned offset) {
    return 0x39400000u | (offset << 10) | (rn << 5) | rt;
}

static uint32_t bf_jit_ldurb_imm9(unsigned rt, unsigned rn, int offset) {
    return 0x38400000u | (((uint32_t)offset & 0x1ffu) << 12) | (rn << 5) | rt;
}

static uint32_t bf_jit_strb_uimm(unsigned rt, unsigned rn) {
    return 0x39000000u | (rn << 5) | rt;
}

static uint32_t bf_jit_strb_uimm_offset(unsigned rt, unsigned rn,
                                        unsigned offset) {
    return 0x39000000u | (offset << 10) | (rn << 5) | rt;
}

static uint32_t bf_jit_sturb_imm9(unsigned rt, unsigned rn, int offset) {
    return 0x38000000u | (((uint32_t)offset & 0x1ffu) << 12) | (rn << 5) | rt;
}

static uint32_t bf_jit_madd_w(unsigned dst, unsigned lhs, unsigned rhs,
                              unsigned addend) {
    return 0x1B000000u | (rhs << 16) | (addend << 10) | (lhs << 5) | dst;
}

static uint32_t bf_jit_add_w_shifted(unsigned dst, unsigned lhs, unsigned rhs,
                                     unsigned shift) {
    return 0x0B000000u | (rhs << 16) | ((shift & 0x3fu) << 10) | (lhs << 5) |
           dst;
}

static uint32_t bf_jit_sub_w_shifted(unsigned dst, unsigned lhs, unsigned rhs,
                                     unsigned shift) {
    return 0x4B000000u | (rhs << 16) | ((shift & 0x3fu) << 10) | (lhs << 5) |
           dst;
}

static uint32_t bf_jit_sub_x_reg(unsigned dst, unsigned lhs, unsigned rhs) {
    return 0xCB000000u | (rhs << 16) | (lhs << 5) | dst;
}

static int bf_jit_emit_load_imm64(bf_jit_emitter *emitter, unsigned reg,
                                  uintptr_t value) {
    return bf_jit_emit_u32(emitter,
                           bf_jit_movz(reg, (uint16_t)(value & 0xffffu), 0)) &&
           bf_jit_emit_u32(
               emitter,
               bf_jit_movk(reg, (uint16_t)((value >> 16) & 0xffffu), 16)) &&
           bf_jit_emit_u32(
               emitter,
               bf_jit_movk(reg, (uint16_t)((value >> 32) & 0xffffu), 32)) &&
           bf_jit_emit_u32(
               emitter,
               bf_jit_movk(reg, (uint16_t)((value >> 48) & 0xffffu), 48));
}

static int bf_jit_emit_load_imm32(bf_jit_emitter *emitter, unsigned reg,
                                  uint32_t value) {
    return bf_jit_emit_u32(
               emitter, bf_jit_movz_w(reg, (uint16_t)(value & 0xffffu), 0)) &&
           (((value >> 16) & 0xffffu) == 0 ||
            bf_jit_emit_u32(
                emitter,
                bf_jit_movk_w(reg, (uint16_t)((value >> 16) & 0xffffu), 16)));
}

static int bf_jit_patch_branch_instruction(bf_jit_emitter *emitter,
                                           size_t patch_offset,
                                           size_t target_offset,
                                           bf_jit_patch_kind kind) {
    int64_t delta_bytes;
    int64_t delta_words;
    uint32_t instruction;
    uint32_t encoded;

    memcpy(&instruction, emitter->code + patch_offset, sizeof(instruction));
    delta_bytes = (int64_t)target_offset - (int64_t)patch_offset;
    delta_words = delta_bytes / 4;

    switch (kind) {
    case BF_JIT_PATCH_BRANCH:
        encoded = instruction | ((uint32_t)delta_words & 0x03ffffffu);
        break;
    case BF_JIT_PATCH_COND:
    case BF_JIT_PATCH_CBZ:
    case BF_JIT_PATCH_CBNZ:
        encoded = instruction | (((uint32_t)delta_words & 0x7ffffu) << 5);
        break;
    default:
        return 0;
    }

    memcpy(emitter->code + patch_offset, &encoded, sizeof(encoded));
    return 1;
}

static int bf_jit_bind_label(bf_jit_emitter *emitter, bf_jit_label *label) {
    size_t index;

    label->position = emitter->length;
    for (index = 0; index < label->patch_count; ++index) {
        if (!bf_jit_patch_branch_instruction(
                emitter, label->patches[index].offset, label->position,
                label->patches[index].kind)) {
            return 0;
        }
    }

    return 1;
}

static int bf_jit_emit_label_ref(bf_jit_emitter *emitter, bf_jit_label *label,
                                 uint32_t instruction,
                                 bf_jit_patch_kind patch_kind) {
    size_t patch_offset;

    patch_offset = emitter->length;
    if (!bf_jit_emit_u32(emitter, instruction)) {
        return 0;
    }

    if (label->position != (size_t)-1) {
        return bf_jit_patch_branch_instruction(emitter, patch_offset,
                                               label->position, patch_kind);
    }

    if (!bf_jit_label_add_patch(label, patch_offset, patch_kind)) {
        bf_set_jit_err(emitter->err, "failed to allocate label patch");
        return 0;
    }

    return 1;
}

static int bf_jit_emit_prologue(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, 0xA9BC7BFDu) &&
           bf_jit_emit_u32(emitter, 0x910003FDu) &&
           bf_jit_emit_u32(emitter, 0xA90153F3u) &&
           bf_jit_emit_u32(emitter, 0x910083F3u) &&
           bf_jit_emit_u32(emitter, 0xF9000260u) &&
           bf_jit_emit_u32(emitter, 0xF9000661u) &&
           bf_jit_emit_u32(emitter, 0xF9000A7Fu);
}

static int bf_jit_emit_success_return(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, 0xF9400A60u) &&
           bf_jit_emit_u32(emitter, 0xA94153F3u) &&
           bf_jit_emit_u32(emitter, 0xA8C47BFDu) &&
           bf_jit_emit_u32(emitter, 0xD65F03C0u);
}

static int bf_jit_emit_failure_return(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, 0xA94153F3u) &&
           bf_jit_emit_u32(emitter, 0xA8C47BFDu) &&
           bf_jit_emit_u32(emitter, 0xD65F03C0u);
}

static int bf_jit_emit_ptr_range_guard(bf_jit_emitter *emitter, int min_offset,
                                       int max_offset, int min_err,
                                       int max_err) {
    if (bf_jit_scoped_guard_covers(emitter, min_offset, max_offset)) {
        return 1;
    }

    if (min_offset < 0) {
        if (!bf_jit_emit_u32(emitter, 0xF9400A68u) ||
            !bf_jit_emit_load_imm64(emitter, 9,
                                    (uintptr_t)(uint64_t)(-min_offset)) ||
            !bf_jit_emit_u32(emitter, bf_jit_cmp_x_reg(8u, 9u)) ||
            !bf_jit_emit_label_ref(emitter, &emitter->error_labels[min_err],
                                   0x54000003u, BF_JIT_PATCH_COND)) {
            return 0;
        }
    }

    if (max_offset > 0) {
        if (!bf_jit_emit_u32(emitter, 0xF9400A68u) ||
            !bf_jit_emit_u32(emitter, bf_jit_mov_x(9u, 8u)) ||
            !bf_jit_emit_add_or_sub_x_imm(emitter, 9u, max_offset) ||
            !bf_jit_emit_u32(emitter, 0xF940066Cu) ||
            !bf_jit_emit_u32(emitter, bf_jit_cmp_x_reg(9u, 12u)) ||
            !bf_jit_emit_label_ref(emitter, &emitter->error_labels[max_err],
                                   0x54000002u, BF_JIT_PATCH_COND)) {
            return 0;
        }
    }

    bf_jit_note_guard_window(emitter, min_offset, max_offset);
    return 1;
}

static int bf_jit_emit_compute_target_ptr(bf_jit_emitter *emitter,
                                          unsigned dst_reg, int offset) {
    return bf_jit_emit_u32(emitter, bf_jit_add_x_reg(dst_reg, 10u, 8u)) &&
           bf_jit_emit_add_or_sub_x_imm(emitter, dst_reg, offset);
}

static int bf_jit_emit_multiply_term(bf_jit_emitter *emitter, unsigned base_reg,
                                     const bf_multiply_term *term) {
    if (term->offset >= -256 && term->offset <= 255) {
        return bf_jit_emit_u32(
                   emitter, bf_jit_ldurb_imm9(13u, base_reg, term->offset)) &&
               bf_jit_emit_load_imm32(emitter, 14u, (uint32_t)term->factor) &&
               bf_jit_emit_u32(emitter, bf_jit_madd_w(13u, 12u, 14u, 13u)) &&
               bf_jit_emit_u32(emitter,
                               bf_jit_sturb_imm9(13u, base_reg, term->offset));
    }

    if (term->offset >= 0 && term->offset <= 4095) {
        return bf_jit_emit_u32(
                   emitter, bf_jit_ldrb_uimm_offset(13u, base_reg,
                                                    (unsigned)term->offset)) &&
               bf_jit_emit_load_imm32(emitter, 14u, (uint32_t)term->factor) &&
               bf_jit_emit_u32(emitter, bf_jit_madd_w(13u, 12u, 14u, 13u)) &&
               bf_jit_emit_u32(emitter, 0x39000000u |
                                            ((uint32_t)term->offset << 10) |
                                            (base_reg << 5) | 13u);
    }

    return bf_jit_emit_compute_target_ptr(emitter, 9u, term->offset) &&
           bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(13u, 9u)) &&
           bf_jit_emit_load_imm32(emitter, 14u, (uint32_t)term->factor) &&
           bf_jit_emit_u32(emitter, bf_jit_madd_w(13u, 12u, 14u, 13u)) &&
           bf_jit_emit_u32(emitter, bf_jit_strb_uimm(13u, 9u));
}

static int bf_jit_emit_load_scan_state(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u);
}

static int bf_jit_emit_store_scan_pointer(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, 0xF9000A68u);
}

static int bf_jit_emit_scan_cell_branch_zero(bf_jit_emitter *emitter,
                                             bf_jit_label *label) {
    return bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
           bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(11u, 15u)) &&
           bf_jit_emit_label_ref(emitter, label, 0x3400000Bu, BF_JIT_PATCH_CBZ);
}

static int bf_jit_emit_scan_cell_branch_nonzero(bf_jit_emitter *emitter,
                                                bf_jit_label *label) {
    return bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
           bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(11u, 15u)) &&
           bf_jit_emit_label_ref(emitter, label, 0x3500000Bu,
                                 BF_JIT_PATCH_CBNZ);
}

static int bf_jit_emit_scan_prepare_upper_bound(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, 0xF940066Cu);
}

static int bf_jit_emit_scan_cell_disp_branch_zero(bf_jit_emitter *emitter,
                                                  int offset,
                                                  bf_jit_label *label) {
    return bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
           bf_jit_emit_u32(
               emitter, bf_jit_ldrb_uimm_offset(11u, 15u, (unsigned)offset)) &&
           bf_jit_emit_label_ref(emitter, label, 0x3400000Bu, BF_JIT_PATCH_CBZ);
}

static int bf_jit_emit_scan_current_oob(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, bf_jit_cmp_x_reg(8u, 12u)) &&
           bf_jit_emit_label_ref(emitter, &emitter->error_labels[3],
                                 0x54000002u, BF_JIT_PATCH_COND);
}

static int bf_jit_emit_scan_advance_oob(bf_jit_emitter *emitter, int delta,
                                        bf_jit_label *label) {
    return bf_jit_emit_u32(emitter, bf_jit_mov_x(9u, 8u)) &&
           bf_jit_emit_add_or_sub_x_imm(emitter, 9u, delta) &&
           bf_jit_emit_u32(emitter, bf_jit_cmp_x_reg(9u, 12u)) &&
           bf_jit_emit_label_ref(emitter, label, 0x54000002u,
                                 BF_JIT_PATCH_COND);
}

static int bf_jit_emit_scan_backward_oob(bf_jit_emitter *emitter, int delta) {
    if (delta >= 0 && delta <= 4095) {
        return bf_jit_emit_u32(emitter,
                               bf_jit_cmp_x_imm(8u, (unsigned)delta)) &&
               bf_jit_emit_label_ref(emitter, &emitter->error_labels[3],
                                     0x54000003u, BF_JIT_PATCH_COND);
    }

    return bf_jit_emit_load_imm64(emitter, 9, (uintptr_t)(uint64_t)delta) &&
           bf_jit_emit_u32(emitter, bf_jit_cmp_x_reg(8u, 9u)) &&
           bf_jit_emit_label_ref(emitter, &emitter->error_labels[3],
                                 0x54000003u, BF_JIT_PATCH_COND);
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
    unsigned start_guard;

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_label_init(&loop_start);
    bf_jit_label_init(&loop_done);

    ok = bf_jit_emit_u32(emitter, 0xF940026Au) &&
         bf_jit_emit_u32(emitter, 0xF9400A68u);

    if (ok && pending_offset > 0) {
        ok = bf_jit_emit_add_or_sub_x_imm(emitter, 8u, pending_offset) &&
             bf_jit_emit_u32(emitter, 0xF940066Cu) &&
             bf_jit_emit_u32(emitter, bf_jit_cmp_x_reg(8u, 12u)) &&
             bf_jit_emit_label_ref(emitter, &emitter->error_labels[1],
                                   0x54000002u, BF_JIT_PATCH_COND);
    } else if (ok && pending_offset < 0) {
        start_guard = (unsigned)(-pending_offset);
        ok = bf_jit_emit_u32(emitter, bf_jit_cmp_x_imm(8u, start_guard)) &&
             bf_jit_emit_label_ref(emitter, &emitter->error_labels[1],
                                   0x54000003u, BF_JIT_PATCH_COND) &&
             bf_jit_emit_add_or_sub_x_imm(emitter, 8u, pending_offset);
    }

    ok = ok && bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
         bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(11u, 15u)) &&
         bf_jit_emit_label_ref(emitter, &loop_done, 0x3400000Bu,
                               BF_JIT_PATCH_CBZ) &&
         bf_jit_bind_label(emitter, &loop_start);

    if (ok && step > 0) {
        ok = bf_jit_emit_add_or_sub_x_imm(emitter, 8u, step) &&
             bf_jit_emit_scan_current_oob(emitter);
    } else if (ok) {
        ok = bf_jit_emit_scan_backward_oob(emitter, -step) &&
             bf_jit_emit_add_or_sub_x_imm(emitter, 8u, step);
    }

    ok = ok && bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
         bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(11u, 15u)) &&
         bf_jit_emit_label_ref(emitter, &loop_start, 0x3500000Bu,
                               BF_JIT_PATCH_CBNZ) &&
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
    return bf_jit_emit_label_ref(context, label, 0x14000000u,
                                 BF_JIT_PATCH_BRANCH);
}

static int bf_jit_emit_scan_invalid_step_cb(void *context) {
    bf_jit_emitter *emitter;

    emitter = context;
    return bf_jit_emit_label_ref(emitter, &emitter->error_labels[3],
                                 0x14000000u, BF_JIT_PATCH_BRANCH);
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
    return bf_jit_emit_scan_cell_branch_zero(context, label);
}

static int bf_jit_emit_scan_current_nonzero_cb(void *context,
                                               bf_jit_label *label) {
    return bf_jit_emit_scan_cell_branch_nonzero(context, label);
}

static int bf_jit_emit_scan_disp_zero_cb(void *context, int offset,
                                         bf_jit_label *label) {
    return bf_jit_emit_scan_cell_disp_branch_zero(context, offset, label);
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
    return bf_jit_emit_add_or_sub_x_imm(context, 8u, delta);
}

static int bf_jit_emit_scan_with_pending_offset_cb(void *context,
                                                   const bf_ir_node *node,
                                                   int pending_offset) {
    bf_jit_emitter *emitter;

    if (!bf_jit_scan_pending_offset_is_whitelisted(node->arg, pending_offset)) {
        return 0;
    }

    emitter = context;
    return bf_jit_emit_op_scan_with_pending_offset(emitter, node->arg,
                                                   pending_offset)
               ? 1
               : -1;
}

static int bf_jit_emit_multiply_with_pending_offset_cb(void *context,
                                                       const bf_ir_node *node,
                                                       int pending_offset) {
    return bf_jit_emit_op_multiply_loop_with_offset((bf_jit_emitter *)context,
                                                    node, pending_offset);
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

static int bf_jit_emit_op_input(bf_jit_emitter *emitter) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_load_imm64(emitter, 16,
                                  (uintptr_t)bf_runtime_read_byte) &&
           bf_jit_emit_u32(emitter, 0xD63F0200u) &&
           bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u) &&
           bf_jit_emit_u32(emitter, 0x38286940u);
}

static int bf_jit_emit_op_output(bf_jit_emitter *emitter) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u) &&
           bf_jit_emit_u32(emitter, 0x38686940u) &&
           bf_jit_emit_load_imm64(emitter, 16,
                                  (uintptr_t)bf_runtime_write_byte) &&
           bf_jit_emit_u32(emitter, 0xD63F0200u);
}

static int bf_jit_emit_op_add_data_offset(bf_jit_emitter *emitter,
                                          const bf_ir_node *node) {
    unsigned value;

    value = (unsigned)((uint8_t)node->arg);
    return bf_jit_emit_ptr_range_guard(emitter, node->offset, node->offset, 8,
                                       9) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_compute_target_ptr(emitter, 9u, node->offset) &&
           bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(11u, 9u)) &&
           bf_jit_emit_u32(
               emitter, value <= 127u
                            ? (0x11000000u | (value << 10) | (11u << 5) | 11u)
                            : (0x51000000u | ((256u - value) << 10) |
                               (11u << 5) | 11u)) &&
           bf_jit_emit_u32(emitter, bf_jit_strb_uimm(11u, 9u));
}

static int bf_jit_emit_op_set_const_offset(bf_jit_emitter *emitter,
                                           const bf_ir_node *node) {
    if ((uint8_t)node->arg == 0) {
        return bf_jit_emit_ptr_range_guard(emitter, node->offset, node->offset,
                                           8, 9) &&
               bf_jit_emit_load_tape_ptr_state(emitter) &&
               bf_jit_emit_compute_target_ptr(emitter, 9u, node->offset) &&
               bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 9u));
    }

    return bf_jit_emit_ptr_range_guard(emitter, node->offset, node->offset, 8,
                                       9) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_compute_target_ptr(emitter, 9u, node->offset) &&
           bf_jit_emit_u32(emitter, 0x52800000u |
                                        ((uint32_t)(uint8_t)node->arg << 5) |
                                        11u) &&
           bf_jit_emit_u32(emitter, bf_jit_strb_uimm(11u, 9u));
}
static int bf_jit_emit_op_scan(bf_jit_emitter *emitter, int step) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_scan_shared(step, &bf_jit_scan_shared_ops, emitter);
}

static int bf_jit_emit_op_multi_zero(bf_jit_emitter *emitter,
                                     const bf_ir_node *node) {
    bf_jit_multi_zero_plan plan;
    size_t term_index;

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_build_multi_zero_plan(node, &plan);

    if (plan.is_noop) {
        return 1;
    }

    if (!bf_jit_emit_ptr_range_guard(emitter, plan.min_offset, plan.max_offset,
                                     8, 9) ||
        !bf_jit_emit_u32(emitter, 0xF940026Au) ||
        !bf_jit_emit_u32(emitter, 0xF9400A68u)) {
        return 0;
    }

    for (term_index = 0; term_index < node->term_count; ++term_index) {
        if (!bf_jit_emit_compute_target_ptr(emitter, 9u,
                                            node->terms[term_index].offset) ||
            !bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 9u))) {
            return 0;
        }
    }

    return bf_jit_emit_add_or_sub_x_imm(emitter, 8u, node->arg) &&
           bf_jit_emit_u32(emitter, 0xF9000A68u);
}

typedef struct bf_jit_aarch64_multiply_term_context {
    bf_jit_emitter *emitter;
    unsigned base_reg;
} bf_jit_aarch64_multiply_term_context;

static int
bf_jit_emit_multiply_term_cb(void *context,
                             const bf_jit_multiply_term_plan *term_plan) {
    bf_jit_aarch64_multiply_term_context *term_context;
    bf_multiply_term term;

    term_context = (bf_jit_aarch64_multiply_term_context *)context;
    term.offset = term_plan->offset;
    term.factor = term_plan->factor;
    return bf_jit_emit_multiply_term(term_context->emitter,
                                     term_context->base_reg, &term);
}

static int bf_jit_emit_op_multiply_loop(bf_jit_emitter *emitter,
                                        const bf_ir_node *node) {
    bf_jit_multiply_loop_plan plan;
    bf_jit_label loop_done;
    bf_jit_aarch64_multiply_term_context term_context;
    int ok;
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_build_multiply_loop_plan(node, &plan);

    if (plan.zero_current_only) {
        return bf_jit_emit_op_set_zero(emitter);
    }

    bf_jit_label_init(&loop_done);

    ok = bf_jit_emit_u32(emitter, 0xF940026Au) &&
         bf_jit_emit_u32(emitter, 0xF9400A68u) &&
         bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
         bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u)) &&
         bf_jit_emit_label_ref(emitter, &loop_done, 0x3400000Cu,
                               BF_JIT_PATCH_CBZ) &&
         bf_jit_emit_ptr_range_guard(emitter, plan.min_offset, plan.max_offset,
                                     4, 5) &&
         bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
         bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u));

    if (ok) {
        term_context.emitter = emitter;
        term_context.base_reg = 15u;
        ok = bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context);
    }

    ok = ok && bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 15u)) &&
         bf_jit_bind_label(emitter, &loop_done);

    bf_jit_label_dispose(&loop_done);
    return ok;
}

static int bf_jit_emit_op_nonnull_multiply_loop(bf_jit_emitter *emitter,
                                                const bf_ir_node *node) {
    bf_jit_multiply_loop_plan plan;
    bf_jit_aarch64_multiply_term_context term_context;
    int ok;
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_build_multiply_loop_plan(node, &plan);

    if (plan.zero_current_only) {
        return bf_jit_emit_op_set_zero(emitter);
    }

    ok = bf_jit_emit_ptr_range_guard(emitter, plan.min_offset, plan.max_offset,
                                     4, 5) &&
         bf_jit_emit_u32(emitter, 0xF940026Au) &&
         bf_jit_emit_u32(emitter, 0xF9400A68u) &&
         bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
         bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u));

    if (ok) {
        term_context.emitter = emitter;
        term_context.base_reg = 15u;
        ok = bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context);
    }

    return ok && bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 15u));
}

static int bf_jit_emit_op_multiply_loop_with_offset(bf_jit_emitter *emitter,
                                                    const bf_ir_node *node,
                                                    int pending_offset) {
    bf_jit_multiply_loop_plan plan;
    bf_jit_aarch64_multiply_term_context term_context;
    bf_jit_label loop_done;
    int combined_min;
    int combined_max;
    int can_use_base_relative_fast_path;
    int ok;
    size_t term_index;
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    bf_jit_invalidate_cached_state(emitter);
    bf_jit_build_multiply_loop_plan(node, &plan);

    if (plan.zero_current_only) {
        return bf_jit_emit_op_set_const_at_offset(emitter, pending_offset, 0)
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

    can_use_base_relative_fast_path = 1;
    for (term_index = 0; term_index < node->term_count; ++term_index) {
        if (node->terms[term_index].offset < -256 ||
            node->terms[term_index].offset > 4095) {
            can_use_base_relative_fast_path = 0;
            break;
        }
    }

    if (node->kind == BF_IR_NONNULL_MULTIPLY_LOOP) {
        if (can_use_base_relative_fast_path) {
            ok = bf_jit_emit_ptr_range_guard(emitter, combined_min,
                                             combined_max, 4, 5) &&
                 bf_jit_emit_load_current_cell_ptr_state_at_offset(
                     emitter, pending_offset) &&
                 bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u));
        } else {
            ok = bf_jit_emit_ptr_range_guard(emitter, combined_min,
                                             combined_max, 4, 5) &&
                 bf_jit_emit_u32(emitter, 0xF940026Au) &&
                 bf_jit_emit_u32(emitter, 0xF9400A68u) &&
                 bf_jit_emit_add_or_sub_x_imm(emitter, 8u, pending_offset) &&
                 bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
                 bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u));
        }

        if (ok) {
            term_context.emitter = emitter;
            term_context.base_reg = 15u;
            ok = bf_jit_emit_multiply_terms_shared(node, &term_ops,
                                                   &term_context);
        }

        return ok && bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 15u)) ? 1
                                                                          : -1;
    }

    bf_jit_label_init(&loop_done);

    if (can_use_base_relative_fast_path) {
        ok = bf_jit_emit_ptr_range_guard(emitter, pending_offset,
                                         pending_offset, 4, 5) &&
             bf_jit_emit_load_current_cell_ptr_state_at_offset(
                 emitter, pending_offset) &&
             bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u)) &&
             bf_jit_emit_label_ref(emitter, &loop_done, 0x3400000Cu,
                                   BF_JIT_PATCH_CBZ) &&
             bf_jit_emit_ptr_range_guard(emitter, combined_min, combined_max, 4,
                                         5) &&
             bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u));
    } else {
        ok = bf_jit_emit_ptr_range_guard(emitter, pending_offset,
                                         pending_offset, 4, 5) &&
             bf_jit_emit_u32(emitter, 0xF940026Au) &&
             bf_jit_emit_u32(emitter, 0xF9400A68u) &&
             bf_jit_emit_add_or_sub_x_imm(emitter, 8u, pending_offset) &&
             bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
             bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u)) &&
             bf_jit_emit_label_ref(emitter, &loop_done, 0x3400000Cu,
                                   BF_JIT_PATCH_CBZ) &&
             bf_jit_emit_ptr_range_guard(emitter, combined_min, combined_max, 4,
                                         5) &&
             bf_jit_emit_add_or_sub_x_imm(emitter, 8u, pending_offset) &&
             bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
             bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u));
    }

    if (ok) {
        term_context.emitter = emitter;
        term_context.base_reg = 15u;
        ok = bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context);
    }

    ok = ok && bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 15u)) &&
         bf_jit_bind_label(emitter, &loop_done);

    bf_jit_label_dispose(&loop_done);
    return ok ? 1 : -1;
}

static int
bf_jit_emit_nonnull_multiply_loop_loaded_state(bf_jit_emitter *emitter,
                                               const bf_ir_node *node) {
    bf_jit_aarch64_multiply_term_context term_context;
    static const bf_jit_multiply_term_ops term_ops = {
        bf_jit_emit_multiply_term_cb,
    };

    if (node->term_count == 0) {
        return bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 15u));
    }

    term_context.emitter = emitter;
    term_context.base_reg = 15u;
    return bf_jit_emit_multiply_terms_shared(node, &term_ops, &term_context) &&
           bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 15u));
}

static int bf_jit_emit_current_cell_branch_zero(bf_jit_emitter *emitter,
                                                bf_jit_label *label) {
    return bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u) &&
           bf_jit_emit_u32(emitter, 0x3868694Bu) &&
           bf_jit_emit_label_ref(emitter, label, 0x3400000Bu, BF_JIT_PATCH_CBZ);
}

static int bf_jit_emit_current_cell_branch_nonzero(bf_jit_emitter *emitter,
                                                   bf_jit_label *label) {
    return bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u) &&
           bf_jit_emit_u32(emitter, 0x3868694Bu) &&
           bf_jit_emit_label_ref(emitter, label, 0x3500000Bu,
                                 BF_JIT_PATCH_CBNZ);
}

static int bf_jit_emit_add_or_sub_x_imm(bf_jit_emitter *emitter, unsigned reg,
                                        int delta) {
    unsigned amount;

    if (delta == 0) {
        return 1;
    }

    amount = (unsigned)(delta < 0 ? -delta : delta);
    while (amount != 0) {
        unsigned chunk;
        uint32_t instruction;

        chunk = amount > 4095u ? 4095u : amount;
        instruction = (delta > 0 ? 0x91000000u : 0xD1000000u) |
                      ((uint32_t)chunk << 10) | (reg << 5) | reg;
        if (!bf_jit_emit_u32(emitter, instruction)) {
            return 0;
        }
        amount -= chunk;
    }

    return 1;
}

static int bf_jit_emit_op_add_ptr(bf_jit_emitter *emitter, int delta) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_u32(emitter, 0xF9400A68u) &&
           bf_jit_emit_add_or_sub_x_imm(emitter, 8u, delta) &&
           bf_jit_emit_u32(emitter, 0xF9400669u) &&
           bf_jit_emit_u32(emitter, 0xEB09011Fu) &&
           bf_jit_emit_label_ref(emitter, &emitter->error_labels[1],
                                 0x54000002u, BF_JIT_PATCH_COND) &&
           bf_jit_emit_u32(emitter, 0xF9000A68u);
}

static int bf_jit_emit_op_add_data(bf_jit_emitter *emitter, int delta) {
    unsigned value;

    bf_jit_invalidate_cached_state(emitter);
    value = (unsigned)((uint8_t)delta);
    return bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u) &&
           bf_jit_emit_u32(emitter, 0x3868694Bu) &&
           bf_jit_emit_u32(
               emitter, value <= 127u
                            ? (0x11000000u | (value << 10) | (11u << 5) | 11u)
                            : (0x51000000u | ((256u - value) << 10) |
                               (11u << 5) | 11u)) &&
           bf_jit_emit_u32(emitter, 0x3828694Bu);
}

static int bf_jit_emit_load_tape_ptr_state(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u);
}

static int bf_jit_emit_load_current_cell_ptr_state(bf_jit_emitter *emitter) {
    return bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u));
}

static int
bf_jit_emit_load_current_cell_ptr_state_at_offset(bf_jit_emitter *emitter,
                                                  int offset) {
    return bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_compute_target_ptr(emitter, 15u, offset);
}

static int bf_jit_emit_load_byte_from_current_cell(bf_jit_emitter *emitter,
                                                   unsigned dst_reg,
                                                   int offset) {
    if (offset == 0) {
        return bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(dst_reg, 15u));
    }
    if (offset > 0 && offset <= 4095) {
        return bf_jit_emit_u32(
            emitter, bf_jit_ldrb_uimm_offset(dst_reg, 15u, (unsigned)offset));
    }
    if (offset >= -256 && offset <= 255) {
        return bf_jit_emit_u32(emitter,
                               bf_jit_ldurb_imm9(dst_reg, 15u, offset));
    }
    return bf_jit_emit_compute_target_ptr(emitter, 9u, offset) &&
           bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(dst_reg, 9u));
}

static int bf_jit_emit_store_byte_from_current_cell(bf_jit_emitter *emitter,
                                                    unsigned src_reg,
                                                    int offset) {
    if (offset == 0) {
        return bf_jit_emit_u32(emitter, bf_jit_strb_uimm(src_reg, 15u));
    }
    if (offset > 0 && offset <= 4095) {
        return bf_jit_emit_u32(
            emitter, bf_jit_strb_uimm_offset(src_reg, 15u, (unsigned)offset));
    }
    if (offset >= -256 && offset <= 255) {
        return bf_jit_emit_u32(emitter,
                               bf_jit_sturb_imm9(src_reg, 15u, offset));
    }
    return bf_jit_emit_compute_target_ptr(emitter, 9u, offset) &&
           bf_jit_emit_u32(emitter, bf_jit_strb_uimm(src_reg, 9u));
}

static int bf_jit_emit_op_set_zero(bf_jit_emitter *emitter) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u) &&
           bf_jit_emit_u32(emitter, 0x3828695Fu);
}

static int bf_jit_emit_op_set_const(bf_jit_emitter *emitter, uint8_t value) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_u32(emitter, 0xF940026Au) &&
           bf_jit_emit_u32(emitter, 0xF9400A68u) &&
           bf_jit_emit_u32(emitter,
                           0x52800000u | ((uint32_t)value << 5) | 11u) &&
           bf_jit_emit_u32(emitter, 0x3828694Bu);
}

static int bf_jit_emit_add_data_with_loaded_ptr(bf_jit_emitter *emitter,
                                                int offset, int delta) {
    unsigned value;

    value = (unsigned)((uint8_t)delta);
    return bf_jit_emit_load_byte_from_current_cell(emitter, 11u, offset) &&
           bf_jit_emit_u32(
               emitter, value <= 127u
                            ? (0x11000000u | (value << 10) | (11u << 5) | 11u)
                            : (0x51000000u | ((256u - value) << 10) |
                               (11u << 5) | 11u)) &&
           bf_jit_emit_store_byte_from_current_cell(emitter, 11u, offset);
}

static int bf_jit_emit_set_const_with_loaded_ptr(bf_jit_emitter *emitter,
                                                 int offset, uint8_t value) {
    if (value == 0) {
        return bf_jit_emit_store_byte_from_current_cell(emitter, 31u, offset);
    }

    return bf_jit_emit_u32(emitter,
                           0x52800000u | ((uint32_t)value << 5) | 11u) &&
           bf_jit_emit_store_byte_from_current_cell(emitter, 11u, offset);
}

static int bf_jit_emit_prepare_simple_run_cursor(bf_jit_emitter *emitter) {
    return bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u));
}

static int bf_jit_emit_move_simple_run_cursor(bf_jit_emitter *emitter,
                                              int *cursor_offset,
                                              int effective_offset) {
    int delta;

    delta = effective_offset - *cursor_offset;
    if (delta == 0) {
        return 1;
    }
    if (!bf_jit_emit_add_or_sub_x_imm(emitter, 15u, delta)) {
        return 0;
    }
    *cursor_offset = effective_offset;
    return 1;
}

static int bf_jit_emit_add_data_at_cursor(bf_jit_emitter *emitter,
                                          uint8_t value) {
    return bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(11u, 15u)) &&
           bf_jit_emit_u32(
               emitter,
               value <= 127u
                   ? (0x11000000u | ((uint32_t)value << 10) | (11u << 5) | 11u)
                   : (0x51000000u | ((uint32_t)(256u - value) << 10) |
                      (11u << 5) | 11u)) &&
           bf_jit_emit_u32(emitter, bf_jit_strb_uimm(11u, 15u));
}

static int bf_jit_emit_set_const_at_cursor(bf_jit_emitter *emitter,
                                           uint8_t value) {
    if (value == 0) {
        return bf_jit_emit_u32(emitter, bf_jit_strb_uimm(31u, 15u));
    }

    return bf_jit_emit_u32(emitter,
                           0x52800000u | ((uint32_t)value << 5) | 11u) &&
           bf_jit_emit_u32(emitter, bf_jit_strb_uimm(11u, 15u));
}

static int bf_jit_emit_op_add_data_at_offset(bf_jit_emitter *emitter,
                                             int offset, int delta) {
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 8, 9) &&
           bf_jit_emit_load_current_cell_ptr_state(emitter) &&
           bf_jit_emit_add_data_with_loaded_ptr(emitter, offset, delta);
}

static int bf_jit_emit_op_set_const_at_offset(bf_jit_emitter *emitter,
                                              int offset, uint8_t value) {
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 8, 9) &&
           bf_jit_emit_load_current_cell_ptr_state(emitter) &&
           bf_jit_emit_set_const_with_loaded_ptr(emitter, offset, value);
}

static int bf_jit_emit_block(bf_jit_emitter *emitter, const bf_ir_block *block);

static int bf_jit_emit_current_cell_branch_zero_at_offset(
    bf_jit_emitter *emitter, int offset, bf_jit_label *label) {
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 1, 1) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_compute_target_ptr(emitter, 15u, offset) &&
           bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(11u, 15u)) &&
           bf_jit_emit_label_ref(emitter, label, 0x3400000Bu, BF_JIT_PATCH_CBZ);
}

static int bf_jit_emit_current_cell_branch_nonzero_at_offset(
    bf_jit_emitter *emitter, int offset, bf_jit_label *label) {
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 1, 1) &&
           bf_jit_emit_load_tape_ptr_state(emitter) &&
           bf_jit_emit_compute_target_ptr(emitter, 15u, offset) &&
           bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(11u, 15u)) &&
           bf_jit_emit_label_ref(emitter, label, 0x3500000Bu,
                                 BF_JIT_PATCH_CBNZ);
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
         bf_jit_emit_current_cell_branch_zero_at_offset(emitter, pending_offset,
                                                        &loop_exit) &&
         bf_jit_emit_block_with_pending_offset(emitter, &node->body,
                                               &body_pending_offset, 0) &&
         body_pending_offset == pending_offset &&
         bf_jit_emit_current_cell_branch_nonzero_at_offset(
             emitter, pending_offset, &loop_start);

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
        bf_jit_multiply_loop_plan multiply_plan;
        int combined_min;
        int combined_max;

        bf_jit_build_multiply_loop_plan(&node->body.nodes[0], &multiply_plan);
        combined_min = pending_offset;
        combined_max = pending_offset;
        if (pending_offset + multiply_plan.min_offset < combined_min) {
            combined_min = pending_offset + multiply_plan.min_offset;
        }
        if (pending_offset + multiply_plan.max_offset > combined_max) {
            combined_max = pending_offset + multiply_plan.max_offset;
        }
        if (pending_offset + tail_info.min_offset < combined_min) {
            combined_min = pending_offset + tail_info.min_offset;
        }
        if (pending_offset + tail_info.max_offset > combined_max) {
            combined_max = pending_offset + tail_info.max_offset;
        }

        ok = bf_jit_emit_current_cell_branch_zero_at_offset(
                 emitter, pending_offset, &if_exit) &&
             bf_jit_emit_ptr_range_guard(emitter, combined_min, combined_max, 4,
                                         5) &&
             bf_jit_emit_load_current_cell_ptr_state_at_offset(
                 emitter, pending_offset) &&
             bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u)) &&
             bf_jit_emit_nonnull_multiply_loop_loaded_state(
                 emitter, &node->body.nodes[0]) &&
             bf_jit_emit_simple_run_with_loaded_ptr_base_offset(
                 emitter, &node->body, 1, &tail_info.next_index,
                 &body_pending_offset, pending_offset) &&
             tail_info.next_index == node->body.count &&
             body_pending_offset == pending_offset;
    } else {
        ok = bf_jit_emit_current_cell_branch_zero_at_offset(
                 emitter, pending_offset, &if_exit) &&
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
         bf_jit_emit_current_cell_branch_zero(emitter, &loop_exit) &&
         bf_jit_emit_block(emitter, &node->body) &&
         bf_jit_emit_current_cell_branch_nonzero(emitter, &loop_start);

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

        ok = bf_jit_emit_current_cell_branch_zero(emitter, &if_exit) &&
             bf_jit_emit_ptr_range_guard(emitter, combined_min, combined_max, 4,
                                         5) &&
             bf_jit_emit_u32(emitter, 0xF940026Au) &&
             bf_jit_emit_u32(emitter, 0xF9400A68u) &&
             bf_jit_emit_u32(emitter, bf_jit_add_x_reg(15u, 10u, 8u)) &&
             bf_jit_emit_u32(emitter, bf_jit_ldrb_uimm(12u, 15u)) &&
             bf_jit_emit_nonnull_multiply_loop_loaded_state(
                 emitter, &node->body.nodes[0]) &&
             bf_jit_emit_simple_run_with_loaded_ptr(
                 emitter, &node->body, 1, &tail_info.next_index,
                 &tail_info.pending_offset_after);
    } else {
        ok = ok && bf_jit_emit_current_cell_branch_zero(emitter, &if_exit) &&
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
    case BF_IR_SET_ZERO:
        return bf_jit_emit_op_set_zero(emitter);
    case BF_IR_SET_CONST:
        return bf_jit_emit_op_set_const(emitter, (uint8_t)node->arg);
    case BF_IR_SET_CONST_OFFSET:
        return bf_jit_emit_op_set_const_offset(emitter, node);
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
        return bf_jit_emit_op_set_const_at_offset(emitter, pending_offset, 0);
    case BF_IR_SET_CONST:
        return bf_jit_emit_op_set_const_at_offset(emitter, pending_offset,
                                                  (uint8_t)node->arg);
    case BF_IR_ADD_DATA_OFFSET:
        return bf_jit_emit_op_add_data_at_offset(
            emitter, pending_offset + node->offset, node->arg);
    case BF_IR_SET_CONST_OFFSET:
        return bf_jit_emit_op_set_const_at_offset(
            emitter, pending_offset + node->offset, (uint8_t)node->arg);
    default:
        return 0;
    }
}

static int bf_jit_emit_simple_effect(bf_jit_emitter *emitter,
                                     int *cursor_offset, int effective_offset,
                                     bf_jit_simple_effect_kind effect_kind,
                                     uint8_t effect_value) {
    if (effect_kind == BF_JIT_SIMPLE_EFFECT_NONE) {
        return 1;
    }
    if (!bf_jit_emit_move_simple_run_cursor(emitter, cursor_offset,
                                            effective_offset)) {
        return 0;
    }
    if (effect_kind == BF_JIT_SIMPLE_EFFECT_ADD) {
        return bf_jit_emit_add_data_at_cursor(emitter, effect_value);
    }
    return bf_jit_emit_set_const_at_cursor(emitter, effect_value);
}

static int bf_jit_emit_simple_effect_with_loaded_ptr(
    bf_jit_emitter *emitter, int effective_offset,
    bf_jit_simple_effect_kind effect_kind, uint8_t effect_value) {
    if (effect_kind == BF_JIT_SIMPLE_EFFECT_NONE) {
        return 1;
    }
    if (effect_kind == BF_JIT_SIMPLE_EFFECT_ADD) {
        return bf_jit_emit_add_data_with_loaded_ptr(emitter, effective_offset,
                                                    effect_value);
    }
    return bf_jit_emit_set_const_with_loaded_ptr(emitter, effective_offset,
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
    if (!bf_jit_emit_simple_effect_with_loaded_ptr(
            emitter, effects.effects[0].effective_offset,
            effects.effects[0].kind, effects.effects[0].value)) {
        return 0;
    }
    if (effects.count == 1) {
        return 1;
    }
    return bf_jit_emit_simple_effect_with_loaded_ptr(
        emitter, effects.effects[1].effective_offset, effects.effects[1].kind,
        effects.effects[1].value);
}

static int bf_jit_emit_simple_run_with_loaded_ptr(bf_jit_emitter *emitter,
                                                  const bf_ir_block *block,
                                                  size_t start_index,
                                                  size_t *next_index,
                                                  int *pending_offset) {
    return bf_jit_emit_simple_run_with_loaded_ptr_base_offset(
        emitter, block, start_index, next_index, pending_offset, 0);
}

static int bf_jit_emit_simple_run_with_loaded_ptr_base_offset(
    bf_jit_emitter *emitter, const bf_ir_block *block, size_t start_index,
    size_t *next_index, int *pending_offset, int base_offset) {
    bf_jit_simple_run_info info;
    int scan_offset;
    int cursor_offset;
    size_t index;
    int pending_effective_offset;
    bf_jit_simple_effect_kind effect_kind;
    uint8_t effect_value;

    bf_jit_collect_simple_run_info(block, start_index, *pending_offset, &info);
    *next_index = info.next_index;

    if (!info.has_simple) {
        *pending_offset = info.pending_offset_after;
        return 1;
    }

    scan_offset = *pending_offset;
    cursor_offset = base_offset;
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
            if (!bf_jit_emit_simple_effect(emitter, &cursor_offset,
                                           pending_effective_offset,
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

    if (!bf_jit_emit_simple_effect(emitter, &cursor_offset,
                                   pending_effective_offset, effect_kind,
                                   effect_value)) {
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
        return bf_jit_emit_set_const_with_loaded_ptr(emitter, effective_offset,
                                                     0);
    case BF_IR_SET_CONST:
    case BF_IR_SET_CONST_OFFSET:
        return bf_jit_emit_set_const_with_loaded_ptr(emitter, effective_offset,
                                                     (uint8_t)node->arg);
    default:
        return 0;
    }
}

static int bf_jit_emit_simple_run(bf_jit_emitter *emitter,
                                  const bf_ir_block *block, size_t start_index,
                                  size_t *next_index, int *pending_offset) {
    bf_jit_simple_run_info info;
    int scan_offset;
    int cursor_offset;
    size_t index;
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
        !bf_jit_emit_load_current_cell_ptr_state(emitter)) {
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

    if (!bf_jit_emit_prepare_simple_run_cursor(emitter)) {
        return 0;
    }

    scan_offset = *pending_offset;
    cursor_offset = 0;
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
            if (!bf_jit_emit_simple_effect(emitter, &cursor_offset,
                                           pending_effective_offset,
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

    if (!bf_jit_emit_simple_effect(emitter, &cursor_offset,
                                   pending_effective_offset, effect_kind,
                                   effect_value)) {
        return 0;
    }

    *pending_offset = info.pending_offset_after;
    return 1;
}

static int bf_jit_emit_input_at_offset(bf_jit_emitter *emitter, int offset) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 8, 9) &&
           bf_jit_emit_load_imm64(emitter, 16,
                                  (uintptr_t)bf_runtime_read_byte) &&
           bf_jit_emit_u32(emitter, 0xD63F0200u) &&
           bf_jit_emit_load_current_cell_ptr_state(emitter) &&
           bf_jit_emit_store_byte_from_current_cell(emitter, 0u, offset);
}

static int bf_jit_emit_output_at_offset(bf_jit_emitter *emitter, int offset) {
    bf_jit_invalidate_cached_state(emitter);
    return bf_jit_emit_ptr_range_guard(emitter, offset, offset, 8, 9) &&
           bf_jit_emit_load_current_cell_ptr_state(emitter) &&
           bf_jit_emit_load_byte_from_current_cell(emitter, 0u, offset) &&
           bf_jit_emit_load_imm64(emitter, 16,
                                  (uintptr_t)bf_runtime_write_byte) &&
           bf_jit_emit_u32(emitter, 0xD63F0200u);
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
           bf_jit_emit_u32(emitter,
                           0x12800000u | ((uint32_t)(reason - 1) << 5)) &&
           bf_jit_emit_failure_return(emitter);
}

static size_t bf_jit_node_size_hint(const bf_ir_node *node, void *context) {
    (void)context;
    switch (node->kind) {
    case BF_IR_ADD_PTR:
        return 28;
    case BF_IR_ADD_DATA:
        return 20;
    case BF_IR_SET_ZERO:
        return 12;
    case BF_IR_SET_CONST:
        return 16;
    case BF_IR_INPUT:
    case BF_IR_OUTPUT:
        return 48;
    case BF_IR_SCAN: {
        bf_jit_scan_plan plan;

        bf_jit_build_scan_plan(node->arg, &plan);
        switch (plan.kind) {
        case BF_JIT_SCAN_PLAN_STEP1:
        case BF_JIT_SCAN_PLAN_STRIDE4:
            return 80;
        case BF_JIT_SCAN_PLAN_GENERIC:
            return 80;
        case BF_JIT_SCAN_PLAN_ERROR:
        default:
            return 80;
        }
    }
    case BF_IR_MULTI_ZERO: {
        bf_jit_multi_zero_plan plan;

        bf_jit_build_multi_zero_plan(node, &plan);
        return 64 + node->term_count * 16 +
               (!plan.is_noop && node->arg != 0 ? 16 : 0);
    }
    case BF_IR_MULTIPLY_LOOP:
    case BF_IR_NONNULL_MULTIPLY_LOOP: {
        bf_jit_multiply_loop_plan plan;

        bf_jit_build_multiply_loop_plan(node, &plan);
        return plan.zero_current_only ? 12 : 96 + node->term_count * 32;
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
        !bf_jit_emit_success_return(&emitter)) {
        bf_jit_emitter_dispose(&emitter);
        return false;
    }

    for (reason = 1; reason <= 9; ++reason) {
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
static const int bf_jit_arch_translation_unit_anchor_aarch64
    __attribute__((used)) = 0;
#endif
