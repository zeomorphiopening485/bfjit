#include "bfjit_internal.h"

#include <string.h>

bool bf_jit_node_is_simple(const bf_ir_node *node) {
    switch (node->kind) {
    case BF_IR_ADD_DATA:
    case BF_IR_SET_ZERO:
    case BF_IR_SET_CONST:
    case BF_IR_ADD_DATA_OFFSET:
    case BF_IR_SET_CONST_OFFSET:
        return true;
    default:
        return false;
    }
}

int bf_jit_simple_node_effective_offset(const bf_ir_node *node,
                                        int pending_offset) {
    switch (node->kind) {
    case BF_IR_ADD_DATA_OFFSET:
    case BF_IR_SET_CONST_OFFSET:
        return pending_offset + node->offset;
    default:
        return pending_offset;
    }
}

bf_jit_simple_effect_kind
bf_jit_simple_node_effect_kind(const bf_ir_node *node) {
    switch (node->kind) {
    case BF_IR_ADD_DATA:
    case BF_IR_ADD_DATA_OFFSET:
        return BF_JIT_SIMPLE_EFFECT_ADD;
    case BF_IR_SET_ZERO:
    case BF_IR_SET_CONST:
    case BF_IR_SET_CONST_OFFSET:
        return BF_JIT_SIMPLE_EFFECT_SET;
    default:
        return BF_JIT_SIMPLE_EFFECT_NONE;
    }
}

uint8_t bf_jit_simple_node_effect_value(const bf_ir_node *node) {
    switch (node->kind) {
    case BF_IR_SET_ZERO:
        return 0;
    case BF_IR_SET_CONST:
    case BF_IR_SET_CONST_OFFSET:
        return (uint8_t)node->arg;
    default:
        return (uint8_t)node->arg;
    }
}

void bf_jit_merge_simple_effect(bf_jit_simple_effect_kind *effect_kind,
                                uint8_t *effect_value,
                                bf_jit_simple_effect_kind next_kind,
                                uint8_t next_value) {
    if (*effect_kind == BF_JIT_SIMPLE_EFFECT_NONE) {
        *effect_kind = next_kind;
        *effect_value = next_value;
    } else if (next_kind == BF_JIT_SIMPLE_EFFECT_ADD) {
        *effect_value = (uint8_t)(*effect_value + next_value);
    } else {
        *effect_kind = BF_JIT_SIMPLE_EFFECT_SET;
        *effect_value = next_value;
    }

    if (*effect_kind == BF_JIT_SIMPLE_EFFECT_ADD && *effect_value == 0) {
        *effect_kind = BF_JIT_SIMPLE_EFFECT_NONE;
    }
}

void bf_jit_collect_simple_run_info(const bf_ir_block *block,
                                    size_t start_index, int pending_offset,
                                    bf_jit_simple_run_info *info) {
    size_t index;
    int scan_offset;

    memset(info, 0, sizeof(*info));
    index = start_index;
    scan_offset = pending_offset;

    while (index < block->count) {
        const bf_ir_node *node;
        int effective_offset;

        node = &block->nodes[index];
        if (node->kind == BF_IR_ADD_PTR) {
            scan_offset += node->arg;
            index += 1;
            continue;
        }
        if (!bf_jit_node_is_simple(node)) {
            break;
        }

        effective_offset =
            bf_jit_simple_node_effective_offset(node, scan_offset);
        if (!info->has_simple) {
            info->min_offset = effective_offset;
            info->max_offset = effective_offset;
            info->has_simple = true;
            info->first_simple_index = index;
            info->first_simple_pending_offset = scan_offset;
        } else {
            if (effective_offset < info->min_offset) {
                info->min_offset = effective_offset;
            }
            if (effective_offset > info->max_offset) {
                info->max_offset = effective_offset;
            }
            if (info->simple_count == 1) {
                info->second_simple_index = index;
                info->second_simple_pending_offset = scan_offset;
            }
        }
        info->simple_count += 1;
        index += 1;
    }

    info->next_index = index;
    info->pending_offset_after = scan_offset;
}

bool bf_jit_if_has_nonnull_multiply_simple_tail(
    const bf_ir_node *node, bf_jit_simple_run_info *tail_info) {
    if (tail_info == NULL) {
        return false;
    }

    memset(tail_info, 0, sizeof(*tail_info));
    if (node == NULL || node->kind != BF_IR_IF || node->body.count < 2 ||
        node->body.nodes[0].kind != BF_IR_NONNULL_MULTIPLY_LOOP) {
        return false;
    }

    bf_jit_collect_simple_run_info(&node->body, 1, 0, tail_info);
    return tail_info->has_simple && tail_info->next_index == node->body.count &&
           tail_info->pending_offset_after == 0;
}

void bf_jit_build_two_simple_effects(const bf_ir_node *first_node,
                                     int first_pending_offset,
                                     const bf_ir_node *second_node,
                                     int second_pending_offset,
                                     bf_jit_two_simple_effects *effects) {
    bf_jit_simple_effect first_effect;
    bf_jit_simple_effect second_effect;

    first_effect.effective_offset =
        bf_jit_simple_node_effective_offset(first_node, first_pending_offset);
    first_effect.kind = bf_jit_simple_node_effect_kind(first_node);
    first_effect.value = bf_jit_simple_node_effect_value(first_node);

    second_effect.effective_offset =
        bf_jit_simple_node_effective_offset(second_node, second_pending_offset);
    second_effect.kind = bf_jit_simple_node_effect_kind(second_node);
    second_effect.value = bf_jit_simple_node_effect_value(second_node);

    effects->count = 0;
    if (first_effect.effective_offset == second_effect.effective_offset) {
        bf_jit_merge_simple_effect(&first_effect.kind, &first_effect.value,
                                   second_effect.kind, second_effect.value);
        if (first_effect.kind != BF_JIT_SIMPLE_EFFECT_NONE) {
            effects->effects[0] = first_effect;
            effects->count = 1;
        }
        return;
    }

    effects->effects[0] = first_effect;
    effects->effects[1] = second_effect;
    effects->count = 2;
}

bool bf_jit_block_is_offset_safe_zero_delta(const bf_ir_block *block) {
    size_t index;
    int delta;

    delta = 0;
    for (index = 0; index < block->count; ++index) {
        const bf_ir_node *node;

        node = &block->nodes[index];
        switch (node->kind) {
        case BF_IR_ADD_PTR:
            delta += node->arg;
            break;
        case BF_IR_ADD_DATA:
        case BF_IR_SET_ZERO:
        case BF_IR_SET_CONST:
        case BF_IR_ADD_DATA_OFFSET:
        case BF_IR_SET_CONST_OFFSET:
        case BF_IR_INPUT:
        case BF_IR_OUTPUT:
            break;
        case BF_IR_IF:
        case BF_IR_LOOP:
            if (!bf_jit_block_is_offset_safe_zero_delta(&node->body)) {
                return false;
            }
            break;
        default:
            return false;
        }
    }

    return delta == 0;
}

void bf_jit_build_control_flow_plan(const bf_ir_node *node, int pending_offset,
                                    bf_jit_control_flow_plan *plan) {
    plan->kind = BF_JIT_CONTROL_FLOW_PLAN_NONE;
    if (pending_offset == 0) {
        return;
    }
    if (!bf_jit_block_is_offset_safe_zero_delta(&node->body)) {
        return;
    }

    if (node->kind == BF_IR_LOOP) {
        plan->kind = BF_JIT_CONTROL_FLOW_PLAN_LOOP_WITH_PENDING_OFFSET;
    } else if (node->kind == BF_IR_IF) {
        plan->kind = BF_JIT_CONTROL_FLOW_PLAN_IF_WITH_PENDING_OFFSET;
    }
}

void bf_jit_build_scan_plan(int step, bf_jit_scan_plan *plan) {
    plan->step = step;
    if (step == 0) {
        plan->kind = BF_JIT_SCAN_PLAN_ERROR;
    } else if (step == 1) {
        plan->kind = BF_JIT_SCAN_PLAN_STEP1;
    } else if (step == 4) {
        plan->kind = BF_JIT_SCAN_PLAN_STRIDE4;
    } else {
        plan->kind = BF_JIT_SCAN_PLAN_GENERIC;
    }
}

int bf_jit_emit_scan_shared(int step, const bf_jit_scan_ops *ops,
                            void *context) {
    bf_jit_scan_plan plan;

    bf_jit_build_scan_plan(step, &plan);

    if (plan.kind == BF_JIT_SCAN_PLAN_ERROR) {
        return ops->emit_invalid_step(context);
    }

    if (plan.kind == BF_JIT_SCAN_PLAN_STEP1) {
        bf_jit_label loop_start;
        bf_jit_label loop_done;
        int ok;

        ops->label_init(&loop_start);
        ops->label_init(&loop_done);
        ok = ops->emit_load_state(context) &&
             ops->emit_branch_current_zero(context, &loop_done) &&
             ops->bind_label(context, &loop_start) &&
             ops->emit_advance(context, 1) &&
             ops->emit_branch_if_current_oob(context) &&
             ops->emit_branch_current_nonzero(context, &loop_start) &&
             ops->bind_label(context, &loop_done) &&
             ops->emit_store_pointer(context);
        ops->label_dispose(&loop_start);
        ops->label_dispose(&loop_done);
        return ok;
    }

    if (plan.kind == BF_JIT_SCAN_PLAN_STRIDE4) {
        bf_jit_label loop_start;
        bf_jit_label loop_done;
        bf_jit_label loop_tail;
        bf_jit_label found_plus4;
        bf_jit_label found_plus8;
        bf_jit_label found_plus12;
        int ok;

        ops->label_init(&loop_start);
        ops->label_init(&loop_done);
        ops->label_init(&loop_tail);
        ops->label_init(&found_plus4);
        ops->label_init(&found_plus8);
        ops->label_init(&found_plus12);

        ok = ops->emit_load_state(context) &&
             ops->emit_prepare_upper_bound(context) &&
             ops->bind_label(context, &loop_start) &&
             ops->emit_branch_if_current_oob(context) &&
             ops->emit_branch_current_zero(context, &loop_done) &&
             ops->emit_branch_if_advance_oob(context, 12, &loop_tail) &&
             ops->emit_branch_disp_zero(context, 4, &found_plus4) &&
             ops->emit_branch_disp_zero(context, 8, &found_plus8) &&
             ops->emit_branch_disp_zero(context, 12, &found_plus12) &&
             ops->emit_advance(context, 16) &&
             ops->emit_jump(context, &loop_start) &&
             ops->bind_label(context, &loop_tail) &&
             ops->emit_advance(context, 4) &&
             ops->emit_jump(context, &loop_start) &&
             ops->bind_label(context, &found_plus4) &&
             ops->emit_advance(context, 4) &&
             ops->emit_jump(context, &loop_done) &&
             ops->bind_label(context, &found_plus8) &&
             ops->emit_advance(context, 8) &&
             ops->emit_jump(context, &loop_done) &&
             ops->bind_label(context, &found_plus12) &&
             ops->emit_advance(context, 12) &&
             ops->bind_label(context, &loop_done) &&
             ops->emit_store_pointer(context);

        ops->label_dispose(&loop_start);
        ops->label_dispose(&loop_done);
        ops->label_dispose(&loop_tail);
        ops->label_dispose(&found_plus4);
        ops->label_dispose(&found_plus8);
        ops->label_dispose(&found_plus12);
        return ok;
    }

    {
        bf_jit_label loop_start;
        bf_jit_label loop_done;
        int ok;

        ops->label_init(&loop_start);
        ops->label_init(&loop_done);

        ok = ops->emit_load_state(context) &&
             (plan.step <= 0 || ops->emit_prepare_upper_bound(context)) &&
             ops->emit_branch_current_zero(context, &loop_done) &&
             ops->bind_label(context, &loop_start);

        if (ok && plan.step > 0) {
            ok = ops->emit_advance(context, plan.step) &&
                 ops->emit_branch_if_current_oob(context);
        } else if (ok) {
            ok = ops->emit_branch_if_backward_oob(context, -plan.step) &&
                 ops->emit_advance(context, plan.step);
        }

        ok = ok && ops->emit_branch_current_nonzero(context, &loop_start) &&
             ops->bind_label(context, &loop_done) &&
             ops->emit_store_pointer(context);

        ops->label_dispose(&loop_start);
        ops->label_dispose(&loop_done);
        return ok;
    }
}

void bf_jit_build_multi_zero_plan(const bf_ir_node *node,
                                  bf_jit_multi_zero_plan *plan) {
    size_t term_index;

    plan->is_noop = node->term_count == 0 && node->arg == 0;
    plan->min_offset = node->arg;
    plan->max_offset = node->arg;
    for (term_index = 0; term_index < node->term_count; ++term_index) {
        if (node->terms[term_index].offset < plan->min_offset) {
            plan->min_offset = node->terms[term_index].offset;
        }
        if (node->terms[term_index].offset > plan->max_offset) {
            plan->max_offset = node->terms[term_index].offset;
        }
    }
}

void bf_jit_build_multiply_loop_plan(const bf_ir_node *node,
                                     bf_jit_multiply_loop_plan *plan) {
    size_t term_index;

    plan->zero_current_only = node->term_count == 0;
    plan->has_terms = node->term_count != 0;
    plan->has_small_term_count = node->term_count <= 2;
    if (node->term_count == 0) {
        plan->min_offset = 0;
        plan->max_offset = 0;
        return;
    }

    plan->min_offset = node->terms[0].offset;
    plan->max_offset = node->terms[0].offset;
    for (term_index = 1; term_index < node->term_count; ++term_index) {
        if (node->terms[term_index].offset < plan->min_offset) {
            plan->min_offset = node->terms[term_index].offset;
        }
        if (node->terms[term_index].offset > plan->max_offset) {
            plan->max_offset = node->terms[term_index].offset;
        }
    }
}

void bf_jit_build_multiply_term_plan(const bf_multiply_term *term,
                                     bf_jit_multiply_term_plan *plan) {
    plan->offset = term->offset;
    plan->factor = term->factor;
    if (term->factor == 1) {
        plan->kind = BF_JIT_MULTIPLY_TERM_PLAN_ADD_SOURCE;
    } else if (term->factor == -1) {
        plan->kind = BF_JIT_MULTIPLY_TERM_PLAN_SUB_SOURCE;
    } else {
        plan->kind = BF_JIT_MULTIPLY_TERM_PLAN_GENERAL;
    }
}

int bf_jit_emit_multiply_terms_shared(const bf_ir_node *node,
                                      const bf_jit_multiply_term_ops *ops,
                                      void *context) {
    size_t term_index;

    for (term_index = 0; term_index < node->term_count; ++term_index) {
        bf_jit_multiply_term_plan plan;

        bf_jit_build_multiply_term_plan(&node->terms[term_index], &plan);
        if (!ops->emit_term(context, &plan)) {
            return 0;
        }
    }

    return 1;
}

size_t bf_jit_block_size_hint_shared(const bf_ir_block *block,
                                     const bf_jit_size_hint_ops *ops) {
    size_t index;
    size_t total;

    total = 0;
    for (index = 0; index < block->count; ++index) {
        const bf_ir_node *node;

        node = &block->nodes[index];
        total += ops->node_size_hint(node, ops->context);
        if (node->kind == BF_IR_LOOP || node->kind == BF_IR_IF) {
            total += bf_jit_block_size_hint_shared(&node->body, ops);
        }
    }

    return total;
}

int bf_jit_emit_block_with_pending_offset_shared(
    const bf_ir_block *block, int *pending_offset, int flush_pending_offset,
    const bf_jit_pending_offset_ops *ops, void *context) {
    size_t index;

    for (index = 0; index < block->count;) {
        const bf_ir_node *node;
        size_t next_index;

        node = &block->nodes[index];
        if (node->kind == BF_IR_ADD_PTR) {
            *pending_offset += node->arg;
            index += 1;
            continue;
        }

        if (bf_jit_node_is_simple(node)) {
            next_index = index;
            if (!ops->emit_simple_run(context, block, index, &next_index,
                                      pending_offset)) {
                return 0;
            }
            index = next_index;
            continue;
        }

        if (*pending_offset != 0) {
            bf_jit_control_flow_plan plan;

            bf_jit_build_control_flow_plan(node, *pending_offset, &plan);
            if (plan.kind != BF_JIT_CONTROL_FLOW_PLAN_NONE) {
                if (!ops->emit_control_with_pending_offset(context, node,
                                                           *pending_offset)) {
                    return 0;
                }
                index += 1;
                continue;
            }
            if (node->kind == BF_IR_INPUT) {
                if (!ops->emit_input_at_offset(context, *pending_offset)) {
                    return 0;
                }
                index += 1;
                continue;
            }
            if (node->kind == BF_IR_OUTPUT) {
                if (!ops->emit_output_at_offset(context, *pending_offset)) {
                    return 0;
                }
                index += 1;
                continue;
            }
            if (node->kind == BF_IR_SCAN &&
                ops->emit_scan_with_pending_offset != NULL) {
                int scan_result;

                scan_result = ops->emit_scan_with_pending_offset(
                    context, node, *pending_offset);
                if (scan_result < 0) {
                    return 0;
                }
                if (scan_result > 0) {
                    *pending_offset = 0;
                    index += 1;
                    continue;
                }
            }
            if ((node->kind == BF_IR_MULTIPLY_LOOP ||
                 node->kind == BF_IR_NONNULL_MULTIPLY_LOOP) &&
                ops->emit_multiply_with_pending_offset != NULL) {
                int multiply_result;

                multiply_result = ops->emit_multiply_with_pending_offset(
                    context, node, *pending_offset);
                if (multiply_result < 0) {
                    return 0;
                }
                if (multiply_result > 0) {
                    index += 1;
                    continue;
                }
            }
            if (!ops->emit_add_ptr(context, *pending_offset)) {
                return 0;
            }
            *pending_offset = 0;
        }

        if (!ops->emit_node(context, node)) {
            return 0;
        }
        index += 1;
    }

    if (flush_pending_offset && *pending_offset != 0 &&
        !ops->emit_add_ptr(context, *pending_offset)) {
        return 0;
    }

    if (flush_pending_offset) {
        *pending_offset = 0;
    }

    return 1;
}
