#define _GNU_SOURCE

#include "bfjit_internal.h"

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void bf_runtime_write_byte(uint8_t value) { putchar_unlocked(value); }

int bf_runtime_read_byte(void) { return getchar_unlocked(); }

size_t bf_runtime_scan_index(const uint8_t *tape, size_t tape_size,
                             size_t start_index, int64_t step) {
    int64_t index;
    int64_t limit;

    if (tape == NULL || step == 0 || start_index >= tape_size) {
        return tape_size;
    }

    index = (int64_t)start_index;
    limit = (int64_t)tape_size;

    while (index >= 0 && index < limit) {
        if (tape[index] == 0) {
            return (size_t)index;
        }
        index += step;
    }

    return tape_size;
}

size_t bf_runtime_scan_index_step4(const uint8_t *tape, size_t tape_size,
                                   size_t start_index) {
    size_t index;

    if (tape == NULL || start_index >= tape_size) {
        return tape_size;
    }

    index = start_index;

    while (index + 12 < tape_size) {
        if (tape[index] == 0) {
            return index;
        }
        if (tape[index + 4] == 0) {
            return index + 4;
        }
        if (tape[index + 8] == 0) {
            return index + 8;
        }
        if (tape[index + 12] == 0) {
            return index + 12;
        }
        index += 16;
    }

    while (index < tape_size) {
        if (tape[index] == 0) {
            return index;
        }
        if (index + 4 < tape_size) {
            index += 4;
        } else {
            break;
        }
    }

    return tape_size;
}

static int bf_runtime_add_offset(size_t pointer, int offset, size_t tape_size,
                                 size_t *result) {
    int64_t next;

    next = (int64_t)pointer + (int64_t)offset;
    if (next < 0 || next >= (int64_t)tape_size) {
        return 0;
    }

    *result = (size_t)next;
    return 1;
}

static int bf_runtime_check_offset_range(size_t pointer, size_t tape_size,
                                         int min_offset, int max_offset,
                                         int min_err, int max_err) {
    size_t ignored;

    if (min_offset < 0 &&
        !bf_runtime_add_offset(pointer, min_offset, tape_size, &ignored)) {
        return -min_err;
    }

    if (max_offset > 0 &&
        !bf_runtime_add_offset(pointer, max_offset, tape_size, &ignored)) {
        return -max_err;
    }

    return 0;
}

static void bf_runtime_profile_record_node(bf_runtime_profile *profile,
                                           const bf_ir_node *node) {
    if (profile == NULL || node == NULL) {
        return;
    }

    profile->total_node_executions += 1;
    if ((size_t)node->kind <= BF_IR_NONNULL_MULTIPLY_LOOP) {
        profile->node_counts[node->kind] += 1;
    }

    if (node->kind == BF_IR_SCAN) {
        if (node->arg == 1) {
            profile->scan_step1_count += 1;
        } else if (node->arg == 4) {
            profile->scan_step4_count += 1;
        } else {
            profile->scan_other_count += 1;
            if (node->arg > 0) {
                profile->scan_other_positive_count += 1;
            } else if (node->arg < 0) {
                profile->scan_other_negative_count += 1;
            }
        }
    } else if (node->kind == BF_IR_MULTIPLY_LOOP ||
               node->kind == BF_IR_NONNULL_MULTIPLY_LOOP) {
        profile->multiply_loop_term_total += node->term_count;
    }
}

static size_t bf_runtime_abs_pointer_delta(size_t lhs, size_t rhs) {
    return lhs >= rhs ? (lhs - rhs) : (rhs - lhs);
}

static void bf_runtime_profile_record_scan_distance(bf_runtime_profile *profile,
                                                    int step,
                                                    size_t start_pointer,
                                                    size_t end_pointer) {
    size_t distance;

    if (profile == NULL) {
        return;
    }

    distance = bf_runtime_abs_pointer_delta(start_pointer, end_pointer);
    if (step == 1) {
        profile->scan_step1_distance_total += distance;
    } else if (step == 4) {
        profile->scan_step4_distance_total += distance;
    } else {
        profile->scan_other_distance_total += distance;
        if (step > 0) {
            profile->scan_other_positive_distance_total += distance;
        } else if (step < 0) {
            profile->scan_other_negative_distance_total += distance;
        }
    }
}

static int bf_runtime_is_simple_segment_node(const bf_ir_node *node) {
    return node->kind == BF_IR_ADD_PTR || node->kind == BF_IR_ADD_DATA ||
           node->kind == BF_IR_SET_ZERO || node->kind == BF_IR_SET_CONST;
}

static int bf_runtime_build_simple_segment_signature(const bf_ir_node *nodes,
                                                     size_t count, char **out) {
    size_t buffer_size;
    size_t index;
    size_t length;
    char *buffer;
    int written;

    buffer_size = count * 24 + 1;
    buffer = malloc(buffer_size);
    if (buffer == NULL) {
        return 0;
    }

    length = 0;
    for (index = 0; index < count; ++index) {
        const bf_ir_node *node;

        node = &nodes[index];
        switch (node->kind) {
        case BF_IR_ADD_PTR:
            written = snprintf(buffer + length, buffer_size - length, "%sP%d",
                               index == 0 ? "" : ",", node->arg);
            break;
        case BF_IR_ADD_DATA:
            written = snprintf(buffer + length, buffer_size - length, "%sD%d",
                               index == 0 ? "" : ",", node->arg);
            break;
        case BF_IR_SET_ZERO:
            written = snprintf(buffer + length, buffer_size - length, "%sZ",
                               index == 0 ? "" : ",");
            break;
        case BF_IR_SET_CONST:
            written = snprintf(buffer + length, buffer_size - length, "%sC%d",
                               index == 0 ? "" : ",", node->arg);
            break;
        default:
            free(buffer);
            return 0;
        }

        if (written < 0 || (size_t)written >= buffer_size - length) {
            free(buffer);
            return 0;
        }
        length += (size_t)written;
    }

    *out = buffer;
    return 1;
}

static const char *bf_runtime_control_flow_kind_code(const bf_ir_node *node) {
    switch (node->kind) {
    case BF_IR_ADD_PTR:
        return "P";
    case BF_IR_ADD_DATA:
        return "D";
    case BF_IR_ADD_DATA_OFFSET:
        return "DO";
    case BF_IR_INPUT:
        return "I";
    case BF_IR_OUTPUT:
        return "O";
    case BF_IR_LOOP:
        return "L";
    case BF_IR_IF:
        return "F";
    case BF_IR_SET_ZERO:
        return "Z";
    case BF_IR_SET_CONST:
        return "C";
    case BF_IR_SET_CONST_OFFSET:
        return "CO";
    case BF_IR_MULTI_ZERO:
        return "MZ";
    case BF_IR_SCAN:
        return "S";
    case BF_IR_MULTIPLY_LOOP:
        return "ML";
    case BF_IR_NONNULL_MULTIPLY_LOOP:
        return "MLN";
    default:
        return "?";
    }
}

static int bf_runtime_append_control_flow_signature_block(
    const bf_ir_block *block, size_t depth, char *buffer, size_t buffer_size,
    size_t *length) {
    size_t index;

    for (index = 0; index < block->count; ++index) {
        const bf_ir_node *node;
        const char *code;
        int written;

        node = &block->nodes[index];
        code = bf_runtime_control_flow_kind_code(node);
        written = snprintf(buffer + *length, buffer_size - *length, "%s%s",
                           index == 0 ? "" : ",", code);
        if (written < 0 || (size_t)written >= buffer_size - *length) {
            return 0;
        }
        *length += (size_t)written;

        if ((node->kind == BF_IR_LOOP || node->kind == BF_IR_IF) && depth > 0) {
            written = snprintf(buffer + *length, buffer_size - *length, "[");
            if (written < 0 || (size_t)written >= buffer_size - *length) {
                return 0;
            }
            *length += (size_t)written;
            if (!bf_runtime_append_control_flow_signature_block(
                    &node->body, depth - 1, buffer, buffer_size, length)) {
                return 0;
            }
            written = snprintf(buffer + *length, buffer_size - *length, "]");
            if (written < 0 || (size_t)written >= buffer_size - *length) {
                return 0;
            }
            *length += (size_t)written;
        }
    }

    return 1;
}

static int bf_runtime_build_control_flow_signature(const bf_ir_node *node,
                                                   char **out_signature) {
    size_t buffer_size;
    size_t length;
    char *buffer;

    if (node == NULL) {
        buffer = malloc(sizeof("<root>"));
        if (buffer == NULL) {
            return 0;
        }
        memcpy(buffer, "<root>", sizeof("<root>"));
        *out_signature = buffer;
        return 1;
    }

    buffer_size = 8192;
    buffer = malloc(buffer_size);
    if (buffer == NULL) {
        return 0;
    }

    length = 0;
    if (!bf_runtime_append_control_flow_signature_block(&node->body, 2, buffer,
                                                        buffer_size, &length)) {
        free(buffer);
        return 0;
    }

    *out_signature = buffer;
    return 1;
}

static int
bf_runtime_profile_ensure_simple_segment_capacity(bf_runtime_profile *profile) {
    size_t new_capacity;
    bf_runtime_simple_segment_entry *new_entries;

    if (profile->simple_segment_entry_count <
        profile->simple_segment_entry_capacity) {
        return 1;
    }

    new_capacity = profile->simple_segment_entry_capacity == 0
                       ? 8
                       : profile->simple_segment_entry_capacity * 2;
    new_entries = realloc(profile->simple_segment_entries,
                          new_capacity * sizeof(*new_entries));
    if (new_entries == NULL) {
        return 0;
    }

    profile->simple_segment_entries = new_entries;
    profile->simple_segment_entry_capacity = new_capacity;
    return 1;
}

static int
bf_runtime_profile_record_simple_segment(bf_runtime_profile *profile,
                                         const bf_ir_node *nodes, size_t count,
                                         const bf_ir_node *context_node) {
    char *signature;
    char *context_signature;
    size_t index;

    if (profile == NULL) {
        return 1;
    }

    if (!bf_runtime_build_simple_segment_signature(nodes, count, &signature)) {
        return 0;
    }

    context_signature = NULL;

    profile->simple_segment_executions += 1;
    profile->simple_segment_total_nodes += count;
    if (count > profile->simple_segment_max_nodes) {
        profile->simple_segment_max_nodes = count;
    }

    for (index = 0; index < profile->simple_segment_entry_count; ++index) {
        if (strcmp(profile->simple_segment_entries[index].signature,
                   signature) == 0 &&
            profile->simple_segment_entries[index].context_node ==
                context_node) {
            profile->simple_segment_entries[index].executions += 1;
            free(signature);
            return 1;
        }
    }

    if (!bf_runtime_profile_ensure_simple_segment_capacity(profile)) {
        free(signature);
        return 0;
    }

    if (!bf_runtime_build_control_flow_signature(context_node,
                                                 &context_signature)) {
        free(signature);
        return 0;
    }

    profile->simple_segment_entries[profile->simple_segment_entry_count]
        .signature = signature;
    profile->simple_segment_entries[profile->simple_segment_entry_count]
        .context_node = context_node;
    profile->simple_segment_entries[profile->simple_segment_entry_count]
        .context_signature = context_signature;
    profile->simple_segment_entries[profile->simple_segment_entry_count]
        .context_kind = context_node == NULL ? BF_IR_LOOP : context_node->kind;
    profile->simple_segment_entries[profile->simple_segment_entry_count]
        .executions = 1;
    profile->simple_segment_entry_count += 1;
    return 1;
}

static int
bf_runtime_profile_ensure_scan_context_capacity(bf_runtime_profile *profile) {
    size_t new_capacity;
    bf_runtime_scan_context_entry *new_entries;

    if (profile->scan_context_entry_count <
        profile->scan_context_entry_capacity) {
        return 1;
    }

    new_capacity = profile->scan_context_entry_capacity == 0
                       ? 8
                       : profile->scan_context_entry_capacity * 2;
    new_entries = realloc(profile->scan_context_entries,
                          new_capacity * sizeof(*new_entries));
    if (new_entries == NULL) {
        return 0;
    }

    profile->scan_context_entries = new_entries;
    profile->scan_context_entry_capacity = new_capacity;
    return 1;
}

static size_t bf_runtime_abs_int_value(int value) {
    return value < 0 ? (size_t)(-(int64_t)value) : (size_t)value;
}

static int bf_runtime_profile_record_scan_context(bf_runtime_profile *profile,
                                                  int pending_offset,
                                                  int step) {
    size_t index;
    size_t abs_offset;

    if (profile == NULL) {
        return 1;
    }

    if (pending_offset != 0) {
        abs_offset = bf_runtime_abs_int_value(pending_offset);
        profile->scan_pending_offset_nonzero_count += 1;
        profile->scan_pending_offset_abs_total += abs_offset;
        if (abs_offset > profile->scan_pending_offset_max_abs) {
            profile->scan_pending_offset_max_abs = abs_offset;
        }
    }

    for (index = 0; index < profile->scan_context_entry_count; ++index) {
        if (profile->scan_context_entries[index].pending_offset ==
                pending_offset &&
            profile->scan_context_entries[index].step == step) {
            profile->scan_context_entries[index].executions += 1;
            return 1;
        }
    }

    if (!bf_runtime_profile_ensure_scan_context_capacity(profile)) {
        return 0;
    }

    profile->scan_context_entries[profile->scan_context_entry_count]
        .pending_offset = pending_offset;
    profile->scan_context_entries[profile->scan_context_entry_count].step =
        step;
    profile->scan_context_entries[profile->scan_context_entry_count]
        .executions = 1;
    profile->scan_context_entry_count += 1;
    return 1;
}

static int bf_runtime_execute_simple_segment(const bf_ir_block *block,
                                             uint8_t *tape, size_t tape_size,
                                             size_t *pointer, size_t *index,
                                             bf_runtime_profile *profile,
                                             const bf_ir_node *context_node) {
    size_t run_start;
    size_t run_end;
    size_t run_index;

    run_start = *index;
    run_end = run_start;
    while (run_end < block->count &&
           bf_runtime_is_simple_segment_node(&block->nodes[run_end])) {
        run_end += 1;
    }

    if (!bf_runtime_profile_record_simple_segment(
            profile, &block->nodes[run_start], run_end - run_start,
            context_node)) {
        return -1;
    }

    for (run_index = run_start; run_index < run_end; ++run_index) {
        const bf_ir_node *node;

        node = &block->nodes[run_index];
        bf_runtime_profile_record_node(profile, node);
        switch (node->kind) {
        case BF_IR_ADD_PTR:
            if (!bf_runtime_add_offset(*pointer, node->arg, tape_size,
                                       pointer)) {
                return -1;
            }
            break;
        case BF_IR_ADD_DATA:
            tape[*pointer] = (uint8_t)(tape[*pointer] + node->arg);
            break;
        case BF_IR_SET_ZERO:
            tape[*pointer] = 0;
            break;
        case BF_IR_SET_CONST:
            tape[*pointer] = (uint8_t)node->arg;
            break;
        default:
            return -1;
        }
    }

    *index = run_end - 1;
    return 0;
}

static int bf_runtime_execute_block(const bf_ir_block *block, uint8_t *tape,
                                    size_t tape_size, size_t *pointer,
                                    bf_runtime_profile *profile,
                                    const bf_ir_node *context_node);

int bf_runtime_execute_scan(bf_jit_state *state, int step) {
    if (state == NULL || state->tape == NULL) {
        return -1;
    }

    if (step == 1) {
        void *found;

        if (state->tape[state->pointer] == 0) {
            return 0;
        }

        found = memchr(state->tape + state->pointer, 0,
                       state->tape_size - state->pointer);
        if (found == NULL) {
            return -2;
        }

        state->pointer = (size_t)((uint8_t *)found - state->tape);
        return 0;
    }

    if (step == 4) {
        state->pointer = bf_runtime_scan_index_step4(
            state->tape, state->tape_size, state->pointer);
    } else {
        state->pointer = bf_runtime_scan_index(state->tape, state->tape_size,
                                               state->pointer, step);
    }

    return state->pointer < state->tape_size ? 0 : -3;
}

int bf_runtime_execute_multi_zero(bf_jit_state *state, const bf_ir_node *node) {
    if (state == NULL || node == NULL || state->tape == NULL) {
        return -1;
    }

    {
        int min_offset;
        int max_offset;
        int range_result;
        size_t term_index;

        min_offset = 0;
        max_offset = 0;
        for (term_index = 0; term_index < node->term_count; ++term_index) {
            if (node->terms[term_index].offset < min_offset) {
                min_offset = node->terms[term_index].offset;
            }
            if (node->terms[term_index].offset > max_offset) {
                max_offset = node->terms[term_index].offset;
            }
        }
        if (node->arg < min_offset) {
            min_offset = node->arg;
        }
        if (node->arg > max_offset) {
            max_offset = node->arg;
        }

        range_result = bf_runtime_check_offset_range(
            state->pointer, state->tape_size, min_offset, max_offset, 8, 9);
        if (range_result < 0) {
            return range_result;
        }

        for (term_index = 0; term_index < node->term_count; ++term_index) {
            size_t target_index;

            if (!bf_runtime_add_offset(state->pointer,
                                       node->terms[term_index].offset,
                                       state->tape_size, &target_index)) {
                return node->terms[term_index].offset < 0 ? -8 : -9;
            }
            state->tape[target_index] = 0;
        }

        if (node->arg != 0 &&
            !bf_runtime_add_offset(state->pointer, node->arg, state->tape_size,
                                   &state->pointer)) {
            return node->arg < 0 ? -8 : -9;
        }

        return 0;
    }
}

int bf_runtime_execute_multiply_loop(bf_jit_state *state,
                                     const bf_ir_node *node) {
    if (state == NULL || node == NULL || state->tape == NULL) {
        return -1;
    }

    if (state->tape[state->pointer] != 0) {
        uint8_t source_value;
        int min_offset;
        int max_offset;
        int range_result;
        size_t term_index;

        if (node->term_count == 0) {
            state->tape[state->pointer] = 0;
            return 0;
        }

        min_offset = node->terms[0].offset;
        max_offset = node->terms[0].offset;
        for (term_index = 1; term_index < node->term_count; ++term_index) {
            if (node->terms[term_index].offset < min_offset) {
                min_offset = node->terms[term_index].offset;
            }
            if (node->terms[term_index].offset > max_offset) {
                max_offset = node->terms[term_index].offset;
            }
        }

        range_result = bf_runtime_check_offset_range(
            state->pointer, state->tape_size, min_offset, max_offset, 4, 5);
        if (range_result < 0) {
            return range_result;
        }

        source_value = state->tape[state->pointer];
        for (term_index = 0; term_index < node->term_count; ++term_index) {
            size_t target_index;

            bf_runtime_add_offset(state->pointer,
                                  node->terms[term_index].offset,
                                  state->tape_size, &target_index);
            state->tape[target_index] =
                (uint8_t)(state->tape[target_index] +
                          source_value * node->terms[term_index].factor);
        }

        state->tape[state->pointer] = 0;
    }

    return 0;
}

static int bf_runtime_execute_block(const bf_ir_block *block, uint8_t *tape,
                                    size_t tape_size, size_t *pointer,
                                    bf_runtime_profile *profile,
                                    const bf_ir_node *context_node) {
    size_t index;
    int jit_pending_offset;

    jit_pending_offset = 0;

    for (index = 0; index < block->count; ++index) {
        const bf_ir_node *node;

        node = &block->nodes[index];
        if (bf_runtime_is_simple_segment_node(node)) {
            int simple_result;
            bf_jit_simple_run_info run_info;

            bf_jit_collect_simple_run_info(block, index, jit_pending_offset,
                                           &run_info);

            simple_result = bf_runtime_execute_simple_segment(
                block, tape, tape_size, pointer, &index, profile, context_node);
            if (simple_result < 0) {
                return simple_result;
            }
            jit_pending_offset = run_info.pending_offset_after;
            continue;
        }

        if (jit_pending_offset != 0) {
            bf_jit_control_flow_plan plan;

            bf_jit_build_control_flow_plan(node, jit_pending_offset, &plan);
            if (node->kind == BF_IR_SCAN) {
                if (!bf_runtime_profile_record_scan_context(
                        profile, jit_pending_offset, node->arg)) {
                    return -1;
                }
                jit_pending_offset = 0;
            } else if (plan.kind == BF_JIT_CONTROL_FLOW_PLAN_NONE &&
                       node->kind != BF_IR_INPUT &&
                       node->kind != BF_IR_OUTPUT) {
                jit_pending_offset = 0;
            }
        } else if (node->kind == BF_IR_SCAN) {
            if (!bf_runtime_profile_record_scan_context(profile, 0,
                                                        node->arg)) {
                return -1;
            }
        }

        bf_runtime_profile_record_node(profile, node);
        switch (node->kind) {
        case BF_IR_ADD_DATA_OFFSET: {
            size_t target_index;

            if (!bf_runtime_add_offset(*pointer, node->offset, tape_size,
                                       &target_index)) {
                return node->offset < 0 ? -8 : -9;
            }
            tape[target_index] = (uint8_t)(tape[target_index] + node->arg);
            break;
        }
        case BF_IR_INPUT:
            tape[*pointer] = (uint8_t)bf_runtime_read_byte();
            break;
        case BF_IR_OUTPUT:
            bf_runtime_write_byte(tape[*pointer]);
            break;
        case BF_IR_LOOP:
            while (tape[*pointer] != 0) {
                int loop_result;

                loop_result = bf_runtime_execute_block(
                    &node->body, tape, tape_size, pointer, profile, node);
                if (loop_result < 0) {
                    return loop_result;
                }
            }
            break;
        case BF_IR_IF:
            if (tape[*pointer] != 0) {
                int if_result;

                if_result = bf_runtime_execute_block(
                    &node->body, tape, tape_size, pointer, profile, node);
                if (if_result < 0) {
                    return if_result;
                }
            }
            break;
        case BF_IR_SET_CONST_OFFSET: {
            size_t target_index;

            if (!bf_runtime_add_offset(*pointer, node->offset, tape_size,
                                       &target_index)) {
                return node->offset < 0 ? -8 : -9;
            }
            tape[target_index] = (uint8_t)node->arg;
            break;
        }
        case BF_IR_SCAN: {
            bf_jit_state state;
            size_t start_pointer;
            int result;

            state.tape = tape;
            state.tape_size = tape_size;
            state.pointer = *pointer;
            start_pointer = *pointer;
            result = bf_runtime_execute_scan(&state, node->arg);
            if (result < 0) {
                return result;
            }
            bf_runtime_profile_record_scan_distance(
                profile, node->arg, start_pointer, state.pointer);
            *pointer = state.pointer;
            break;
        }
        case BF_IR_MULTI_ZERO: {
            bf_jit_state state;
            int result;

            state.tape = tape;
            state.tape_size = tape_size;
            state.pointer = *pointer;
            result = bf_runtime_execute_multi_zero(&state, node);
            if (result < 0) {
                return result;
            }
            *pointer = state.pointer;
            break;
        }
        case BF_IR_MULTIPLY_LOOP:
        case BF_IR_NONNULL_MULTIPLY_LOOP: {
            bf_jit_state state;
            int result;

            state.tape = tape;
            state.tape_size = tape_size;
            state.pointer = *pointer;
            result = bf_runtime_execute_multiply_loop(&state, node);
            if (result < 0) {
                return result;
            }
            *pointer = state.pointer;
            break;
        }
        default:
            return -1;
        }
    }

    if (*pointer > INT_MAX) {
        return -1;
    }

    return 0;
}

void bf_runtime_profile_dispose(bf_runtime_profile *profile) {
    size_t index;

    if (profile == NULL) {
        return;
    }

    for (index = 0; index < profile->simple_segment_entry_count; ++index) {
        free(profile->simple_segment_entries[index].signature);
        free(profile->simple_segment_entries[index].context_signature);
    }

    free(profile->simple_segment_entries);
    profile->simple_segment_entries = NULL;
    profile->simple_segment_entry_count = 0;
    profile->simple_segment_entry_capacity = 0;

    free(profile->scan_context_entries);
    profile->scan_context_entries = NULL;
    profile->scan_context_entry_count = 0;
    profile->scan_context_entry_capacity = 0;
}

int bf_runtime_execute(const bf_program *program, uint8_t *tape,
                       size_t tape_size) {
    return bf_runtime_execute_profiled(program, tape, tape_size, NULL);
}

int bf_runtime_execute_profiled(const bf_program *program, uint8_t *tape,
                                size_t tape_size, bf_runtime_profile *profile) {
    size_t pointer;
    int result;

    if (program == NULL || tape == NULL) {
        return -1;
    }

    if (profile != NULL) {
        memset(profile, 0, sizeof(*profile));
    }

    pointer = 0;
    result = bf_runtime_execute_block(&program->root, tape, tape_size, &pointer,
                                      profile, NULL);
    if (result < 0) {
        return result;
    }

    if (pointer > INT_MAX) {
        return -1;
    }

    return (int)pointer;
}
