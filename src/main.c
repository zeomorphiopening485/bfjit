#include "bfjit.h"
#include "bfjit_internal.h"
#include "bfopt.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct bf_multiply_histogram_entry {
    size_t term_count;
    size_t occurrences;
} bf_multiply_histogram_entry;

typedef struct bf_multiply_signature_entry {
    char *signature;
    size_t occurrences;
} bf_multiply_signature_entry;

typedef struct bf_multiply_stats {
    size_t total_loops;
    size_t total_terms;
    size_t max_term_count;
    bf_multiply_histogram_entry *histogram;
    size_t histogram_count;
    size_t histogram_capacity;
    bf_multiply_signature_entry *signatures;
    size_t signature_count;
    size_t signature_capacity;
} bf_multiply_stats;

typedef struct bf_profile_entry {
    bf_ir_kind kind;
    size_t count;
} bf_profile_entry;

typedef struct bf_simple_segment_signature_entry {
    char *signature;
    size_t occurrences;
} bf_simple_segment_signature_entry;

typedef struct bf_simple_segment_stats {
    size_t total_segments;
    size_t total_nodes;
    size_t max_nodes;
    bf_simple_segment_signature_entry *signatures;
    size_t signature_count;
    size_t signature_capacity;
} bf_simple_segment_stats;

typedef struct bf_control_flow_stats {
    size_t loop_count;
    size_t if_count;
    size_t max_depth;
    size_t loops_with_nested_cf;
    size_t ifs_with_nested_cf;
    size_t loops_with_scan;
    size_t loops_with_multiply;
    size_t loops_with_multi_zero;
    size_t zero_delta_loops;
    size_t zero_delta_ifs;
    size_t if_convertible_loops;
    size_t nested_cf_only_candidate_loops;
    size_t scan_blocked_loops;
    size_t origin_blocked_loops;
    size_t delta_blocked_loops;
    size_t origin_not_zero_blocked_loops;
    struct bf_control_flow_signature_entry *nested_candidate_signatures;
    size_t nested_candidate_signature_count;
    size_t nested_candidate_signature_capacity;
} bf_control_flow_stats;

typedef struct bf_control_flow_signature_entry {
    char *signature;
    size_t occurrences;
} bf_control_flow_signature_entry;

typedef struct bf_loop_if_analysis {
    int final_offset;
    int origin_zero;
    int touches_origin_badly;
    int has_nested_cf;
    int has_scan;
    int has_multiply;
    int has_multi_zero;
} bf_loop_if_analysis;

static int bf_read_file(const char *path, char **contents, size_t *length) {
    FILE *stream;
    long file_size;
    char *buf;
    size_t read_count;

    stream = fopen(path, "rb");
    if (stream == NULL) {
        return 0;
    }

    if (fseek(stream, 0, SEEK_END) != 0) {
        fclose(stream);
        return 0;
    }

    file_size = ftell(stream);
    if (file_size < 0) {
        fclose(stream);
        return 0;
    }

    if (fseek(stream, 0, SEEK_SET) != 0) {
        fclose(stream);
        return 0;
    }

    buf = malloc((size_t)file_size + 1);
    if (buf == NULL) {
        fclose(stream);
        return 0;
    }

    read_count = fread(buf, 1, (size_t)file_size, stream);
    fclose(stream);
    if (read_count != (size_t)file_size) {
        free(buf);
        return 0;
    }

    buf[file_size] = '\0';
    *contents = buf;
    *length = (size_t)file_size;
    return 1;
}

static void bf_multiply_stats_dispose(bf_multiply_stats *stats) {
    size_t index;

    if (stats == NULL) {
        return;
    }

    for (index = 0; index < stats->signature_count; ++index) {
        free(stats->signatures[index].signature);
    }

    free(stats->histogram);
    free(stats->signatures);
    memset(stats, 0, sizeof(*stats));
}

static void bf_simple_segment_stats_dispose(bf_simple_segment_stats *stats) {
    size_t index;

    if (stats == NULL) {
        return;
    }

    for (index = 0; index < stats->signature_count; ++index) {
        free(stats->signatures[index].signature);
    }

    free(stats->signatures);
    memset(stats, 0, sizeof(*stats));
}

static void bf_control_flow_stats_dispose(bf_control_flow_stats *stats) {
    size_t index;

    if (stats == NULL) {
        return;
    }

    for (index = 0; index < stats->nested_candidate_signature_count; ++index) {
        free(stats->nested_candidate_signatures[index].signature);
    }

    free(stats->nested_candidate_signatures);
    memset(stats, 0, sizeof(*stats));
}

static int
bf_control_flow_stats_ensure_signature_capacity(bf_control_flow_stats *stats) {
    size_t new_capacity;
    bf_control_flow_signature_entry *new_entries;

    if (stats->nested_candidate_signature_count <
        stats->nested_candidate_signature_capacity) {
        return 1;
    }

    new_capacity = stats->nested_candidate_signature_capacity == 0
                       ? 8
                       : stats->nested_candidate_signature_capacity * 2;
    new_entries = realloc(stats->nested_candidate_signatures,
                          new_capacity * sizeof(*new_entries));
    if (new_entries == NULL) {
        return 0;
    }

    stats->nested_candidate_signatures = new_entries;
    stats->nested_candidate_signature_capacity = new_capacity;
    return 1;
}

static const char *bf_control_flow_kind_code(const bf_ir_node *node) {
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

static int bf_append_control_flow_signature_block(const bf_ir_block *block,
                                                  size_t depth, char *buffer,
                                                  size_t buffer_size,
                                                  size_t *length) {
    size_t index;

    for (index = 0; index < block->count; ++index) {
        const bf_ir_node *node;
        const char *code;
        int written;

        node = &block->nodes[index];
        code = bf_control_flow_kind_code(node);
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
            if (!bf_append_control_flow_signature_block(
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

static int bf_build_control_flow_signature(const bf_ir_node *node,
                                           char **out_signature) {
    size_t buffer_size;
    size_t length;
    char *buffer;

    buffer_size = 8192;
    buffer = malloc(buffer_size);
    if (buffer == NULL) {
        return 0;
    }

    length = 0;
    if (!bf_append_control_flow_signature_block(&node->body, 2, buffer,
                                                buffer_size, &length)) {
        free(buffer);
        return 0;
    }

    *out_signature = buffer;
    return 1;
}

static int bf_record_nested_candidate_signature(bf_control_flow_stats *stats,
                                                const bf_ir_node *node) {
    char *signature;
    size_t index;

    if (!bf_build_control_flow_signature(node, &signature)) {
        return 0;
    }

    for (index = 0; index < stats->nested_candidate_signature_count; ++index) {
        if (strcmp(stats->nested_candidate_signatures[index].signature,
                   signature) == 0) {
            stats->nested_candidate_signatures[index].occurrences += 1;
            free(signature);
            return 1;
        }
    }

    if (!bf_control_flow_stats_ensure_signature_capacity(stats)) {
        free(signature);
        return 0;
    }

    stats->nested_candidate_signatures[stats->nested_candidate_signature_count]
        .signature = signature;
    stats->nested_candidate_signatures[stats->nested_candidate_signature_count]
        .occurrences = 1;
    stats->nested_candidate_signature_count += 1;
    return 1;
}

static int bf_compare_control_flow_signature_entries(const void *lhs,
                                                     const void *rhs) {
    const bf_control_flow_signature_entry *left;
    const bf_control_flow_signature_entry *right;

    left = lhs;
    right = rhs;
    if (left->occurrences > right->occurrences) {
        return -1;
    }
    if (left->occurrences < right->occurrences) {
        return 1;
    }
    return strcmp(left->signature, right->signature);
}

static int bf_control_multi_zero_touches_origin(const bf_ir_node *node,
                                                int current_offset) {
    size_t term_index;

    for (term_index = 0; term_index < node->term_count; ++term_index) {
        if (current_offset + node->terms[term_index].offset == 0) {
            return 1;
        }
    }

    return 0;
}

static int bf_control_multiply_loop_may_touch_origin(const bf_ir_node *node,
                                                     int current_offset) {
    size_t term_index;

    if (current_offset == 0) {
        return 1;
    }

    for (term_index = 0; term_index < node->term_count; ++term_index) {
        if (current_offset + node->terms[term_index].offset == 0) {
            return 1;
        }
    }

    return 0;
}

static void bf_analyze_loop_if_candidate(const bf_ir_node *node,
                                         bf_loop_if_analysis *analysis) {
    int current_offset;
    size_t index;

    memset(analysis, 0, sizeof(*analysis));
    if (node->kind != BF_IR_LOOP && node->kind != BF_IR_IF) {
        return;
    }

    current_offset = 0;
    for (index = 0; index < node->body.count; ++index) {
        const bf_ir_node *body_node;

        body_node = &node->body.nodes[index];
        switch (body_node->kind) {
        case BF_IR_ADD_PTR:
            current_offset += body_node->arg;
            break;
        case BF_IR_SET_ZERO:
            if (current_offset == 0) {
                analysis->origin_zero = 1;
            }
            break;
        case BF_IR_SET_CONST:
            if (current_offset == 0) {
                analysis->origin_zero = (body_node->arg == 0);
            }
            break;
        case BF_IR_SET_CONST_OFFSET:
            if (current_offset + body_node->offset == 0) {
                analysis->origin_zero = (body_node->arg == 0);
            }
            break;
        case BF_IR_ADD_DATA:
        case BF_IR_INPUT:
            if (current_offset == 0) {
                analysis->touches_origin_badly = 1;
            }
            break;
        case BF_IR_ADD_DATA_OFFSET:
            if (current_offset + body_node->offset == 0) {
                analysis->touches_origin_badly = 1;
            }
            break;
        case BF_IR_OUTPUT:
            break;
        case BF_IR_SCAN:
            analysis->has_scan = 1;
            break;
        case BF_IR_LOOP:
        case BF_IR_IF:
            analysis->has_nested_cf = 1;
            break;
        case BF_IR_MULTI_ZERO:
            analysis->has_multi_zero = 1;
            if (bf_control_multi_zero_touches_origin(body_node,
                                                     current_offset)) {
                analysis->origin_zero = 1;
            }
            current_offset += body_node->arg;
            break;
        case BF_IR_MULTIPLY_LOOP:
        case BF_IR_NONNULL_MULTIPLY_LOOP:
            analysis->has_multiply = 1;
            if (bf_control_multiply_loop_may_touch_origin(body_node,
                                                          current_offset)) {
                if (current_offset != 0) {
                    analysis->touches_origin_badly = 1;
                } else {
                    analysis->origin_zero = 1;
                }
            }
            break;
        default:
            analysis->touches_origin_badly = 1;
            break;
        }
    }

    analysis->final_offset = current_offset;
}

static int bf_collect_control_flow_stats_block(const bf_ir_block *block,
                                               bf_control_flow_stats *stats,
                                               size_t depth) {
    size_t index;

    if (depth > stats->max_depth) {
        stats->max_depth = depth;
    }

    for (index = 0; index < block->count; ++index) {
        const bf_ir_node *node;

        node = &block->nodes[index];
        if (node->kind == BF_IR_LOOP || node->kind == BF_IR_IF) {
            bf_loop_if_analysis analysis;

            bf_analyze_loop_if_candidate(node, &analysis);
            if (node->kind == BF_IR_LOOP) {
                stats->loop_count += 1;
                if (analysis.has_nested_cf) {
                    stats->loops_with_nested_cf += 1;
                }
                if (analysis.has_scan) {
                    stats->loops_with_scan += 1;
                }
                if (analysis.has_multiply) {
                    stats->loops_with_multiply += 1;
                }
                if (analysis.has_multi_zero) {
                    stats->loops_with_multi_zero += 1;
                }
                if (analysis.final_offset == 0) {
                    stats->zero_delta_loops += 1;
                }
                if (analysis.final_offset == 0 && analysis.origin_zero &&
                    !analysis.touches_origin_badly && !analysis.has_nested_cf &&
                    !analysis.has_scan) {
                    stats->if_convertible_loops += 1;
                } else if (analysis.final_offset == 0 && analysis.origin_zero &&
                           !analysis.touches_origin_badly &&
                           analysis.has_nested_cf && !analysis.has_scan) {
                    stats->nested_cf_only_candidate_loops += 1;
                    if (!bf_record_nested_candidate_signature(stats, node)) {
                        return 0;
                    }
                } else {
                    if (analysis.has_scan) {
                        stats->scan_blocked_loops += 1;
                    }
                    if (analysis.touches_origin_badly) {
                        stats->origin_blocked_loops += 1;
                    }
                    if (analysis.final_offset != 0) {
                        stats->delta_blocked_loops += 1;
                    }
                    if (!analysis.origin_zero) {
                        stats->origin_not_zero_blocked_loops += 1;
                    }
                }
            } else {
                stats->if_count += 1;
                if (analysis.has_nested_cf) {
                    stats->ifs_with_nested_cf += 1;
                }
                if (analysis.final_offset == 0) {
                    stats->zero_delta_ifs += 1;
                }
            }

            if (!bf_collect_control_flow_stats_block(&node->body, stats,
                                                     depth + 1)) {
                return 0;
            }
        }
    }

    return 1;
}

static void bf_dump_control_flow_stats(const bf_program *program,
                                       const char *program_path,
                                       const char *phase_label) {
    bf_control_flow_stats stats;
    size_t index;
    size_t preview_count;

    memset(&stats, 0, sizeof(stats));
    if (!bf_collect_control_flow_stats_block(&program->root, &stats, 1)) {
        fprintf(stderr, "failed to collect control-flow stats\n");
        bf_control_flow_stats_dispose(&stats);
        return;
    }

    qsort(stats.nested_candidate_signatures,
          stats.nested_candidate_signature_count,
          sizeof(*stats.nested_candidate_signatures),
          bf_compare_control_flow_signature_entries);

    printf("control-flow stats for %s (%s)\n", program_path, phase_label);
    printf("loop_count: %zu\n", stats.loop_count);
    printf("if_count: %zu\n", stats.if_count);
    printf("max_depth: %zu\n", stats.max_depth);
    printf("zero_delta_loops: %zu\n", stats.zero_delta_loops);
    printf("zero_delta_ifs: %zu\n", stats.zero_delta_ifs);
    printf("loops_with_nested_cf: %zu\n", stats.loops_with_nested_cf);
    printf("ifs_with_nested_cf: %zu\n", stats.ifs_with_nested_cf);
    printf("loops_with_scan: %zu\n", stats.loops_with_scan);
    printf("loops_with_multiply: %zu\n", stats.loops_with_multiply);
    printf("loops_with_multi_zero: %zu\n", stats.loops_with_multi_zero);
    printf("if_convertible_loops: %zu\n", stats.if_convertible_loops);
    printf("nested_cf_only_candidate_loops: %zu\n",
           stats.nested_cf_only_candidate_loops);
    printf("scan_blocked_loops: %zu\n", stats.scan_blocked_loops);
    printf("origin_blocked_loops: %zu\n", stats.origin_blocked_loops);
    printf("delta_blocked_loops: %zu\n", stats.delta_blocked_loops);
    printf("origin_not_zero_blocked_loops: %zu\n",
           stats.origin_not_zero_blocked_loops);

    if (stats.nested_candidate_signature_count != 0) {
        puts("top nested candidate signatures:");
        preview_count = stats.nested_candidate_signature_count < 12
                            ? stats.nested_candidate_signature_count
                            : 12;
        for (index = 0; index < preview_count; ++index) {
            printf("  %zu x %s\n",
                   stats.nested_candidate_signatures[index].occurrences,
                   stats.nested_candidate_signatures[index].signature);
        }
    }

    bf_control_flow_stats_dispose(&stats);
}

static int bf_simple_segment_stats_ensure_signature_capacity(
    bf_simple_segment_stats *stats) {
    size_t new_capacity;
    bf_simple_segment_signature_entry *new_entries;

    if (stats->signature_count < stats->signature_capacity) {
        return 1;
    }

    new_capacity =
        stats->signature_capacity == 0 ? 8 : stats->signature_capacity * 2;
    new_entries =
        realloc(stats->signatures, new_capacity * sizeof(*new_entries));
    if (new_entries == NULL) {
        return 0;
    }

    stats->signatures = new_entries;
    stats->signature_capacity = new_capacity;
    return 1;
}

static int bf_is_simple_segment_node(const bf_ir_node *node) {
    return node->kind == BF_IR_ADD_PTR || node->kind == BF_IR_ADD_DATA ||
           node->kind == BF_IR_SET_ZERO || node->kind == BF_IR_SET_CONST;
}

static int bf_build_simple_segment_signature(const bf_ir_node *nodes,
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

static int bf_simple_segment_stats_record_signature(
    bf_simple_segment_stats *stats, const bf_ir_node *nodes, size_t count) {
    char *signature;
    size_t index;

    if (!bf_build_simple_segment_signature(nodes, count, &signature)) {
        return 0;
    }

    for (index = 0; index < stats->signature_count; ++index) {
        if (strcmp(stats->signatures[index].signature, signature) == 0) {
            stats->signatures[index].occurrences += 1;
            free(signature);
            return 1;
        }
    }

    if (!bf_simple_segment_stats_ensure_signature_capacity(stats)) {
        free(signature);
        return 0;
    }

    stats->signatures[stats->signature_count].signature = signature;
    stats->signatures[stats->signature_count].occurrences = 1;
    stats->signature_count += 1;
    return 1;
}

static int
bf_collect_simple_segment_stats_block(const bf_ir_block *block,
                                      bf_simple_segment_stats *stats) {
    size_t index;

    index = 0;
    while (index < block->count) {
        size_t start_index;

        while (index < block->count &&
               !bf_is_simple_segment_node(&block->nodes[index])) {
            if ((block->nodes[index].kind == BF_IR_LOOP ||
                 block->nodes[index].kind == BF_IR_IF) &&
                !bf_collect_simple_segment_stats_block(
                    &block->nodes[index].body, stats)) {
                return 0;
            }
            index += 1;
        }

        start_index = index;
        while (index < block->count &&
               bf_is_simple_segment_node(&block->nodes[index])) {
            index += 1;
        }

        if (index > start_index) {
            size_t count;

            count = index - start_index;
            stats->total_segments += 1;
            stats->total_nodes += count;
            if (count > stats->max_nodes) {
                stats->max_nodes = count;
            }
            if (!bf_simple_segment_stats_record_signature(
                    stats, &block->nodes[start_index], count)) {
                return 0;
            }
        }
    }

    return 1;
}

static int
bf_multiply_stats_ensure_histogram_capacity(bf_multiply_stats *stats) {
    size_t new_capacity;
    bf_multiply_histogram_entry *new_entries;

    if (stats->histogram_count < stats->histogram_capacity) {
        return 1;
    }

    new_capacity =
        stats->histogram_capacity == 0 ? 8 : stats->histogram_capacity * 2;
    new_entries =
        realloc(stats->histogram, new_capacity * sizeof(*new_entries));
    if (new_entries == NULL) {
        return 0;
    }

    stats->histogram = new_entries;
    stats->histogram_capacity = new_capacity;
    return 1;
}

static int
bf_multiply_stats_ensure_signature_capacity(bf_multiply_stats *stats) {
    size_t new_capacity;
    bf_multiply_signature_entry *new_entries;

    if (stats->signature_count < stats->signature_capacity) {
        return 1;
    }

    new_capacity =
        stats->signature_capacity == 0 ? 8 : stats->signature_capacity * 2;
    new_entries =
        realloc(stats->signatures, new_capacity * sizeof(*new_entries));
    if (new_entries == NULL) {
        return 0;
    }

    stats->signatures = new_entries;
    stats->signature_capacity = new_capacity;
    return 1;
}

static int bf_multiply_stats_record_term_count(bf_multiply_stats *stats,
                                               size_t term_count) {
    size_t index;

    for (index = 0; index < stats->histogram_count; ++index) {
        if (stats->histogram[index].term_count == term_count) {
            stats->histogram[index].occurrences += 1;
            return 1;
        }
    }

    if (!bf_multiply_stats_ensure_histogram_capacity(stats)) {
        return 0;
    }

    stats->histogram[stats->histogram_count].term_count = term_count;
    stats->histogram[stats->histogram_count].occurrences = 1;
    stats->histogram_count += 1;
    return 1;
}

static int bf_build_multiply_signature(const bf_ir_node *node, char **out) {
    size_t buffer_size;
    size_t length;
    size_t index;
    char *buffer;
    int written;

    buffer_size = node->term_count == 0 ? 16 : node->term_count * 32 + 1;
    buffer = malloc(buffer_size);
    if (buffer == NULL) {
        return 0;
    }

    length = 0;
    for (index = 0; index < node->term_count; ++index) {
        written = snprintf(buffer + length, buffer_size - length, "%s%d:%d",
                           index == 0 ? "" : ",", node->terms[index].offset,
                           node->terms[index].factor);
        if (written < 0 || (size_t)written >= buffer_size - length) {
            free(buffer);
            return 0;
        }
        length += (size_t)written;
    }

    if (node->term_count == 0) {
        memcpy(buffer, "origin-only", sizeof("origin-only"));
    }

    *out = buffer;
    return 1;
}

static int bf_multiply_stats_record_signature(bf_multiply_stats *stats,
                                              const bf_ir_node *node) {
    char *signature;
    size_t index;

    if (!bf_build_multiply_signature(node, &signature)) {
        return 0;
    }

    for (index = 0; index < stats->signature_count; ++index) {
        if (strcmp(stats->signatures[index].signature, signature) == 0) {
            stats->signatures[index].occurrences += 1;
            free(signature);
            return 1;
        }
    }

    if (!bf_multiply_stats_ensure_signature_capacity(stats)) {
        free(signature);
        return 0;
    }

    stats->signatures[stats->signature_count].signature = signature;
    stats->signatures[stats->signature_count].occurrences = 1;
    stats->signature_count += 1;
    return 1;
}

static int bf_collect_multiply_stats_block(const bf_ir_block *block,
                                           bf_multiply_stats *stats) {
    size_t index;

    for (index = 0; index < block->count; ++index) {
        const bf_ir_node *node;

        node = &block->nodes[index];
        if (node->kind == BF_IR_MULTIPLY_LOOP ||
            node->kind == BF_IR_NONNULL_MULTIPLY_LOOP) {
            stats->total_loops += 1;
            stats->total_terms += node->term_count;
            if (node->term_count > stats->max_term_count) {
                stats->max_term_count = node->term_count;
            }
            if (!bf_multiply_stats_record_term_count(stats, node->term_count) ||
                !bf_multiply_stats_record_signature(stats, node)) {
                return 0;
            }
        }

        if ((node->kind == BF_IR_LOOP || node->kind == BF_IR_IF) &&
            !bf_collect_multiply_stats_block(&node->body, stats)) {
            return 0;
        }
    }

    return 1;
}

static int bf_compare_histogram_entries(const void *lhs, const void *rhs) {
    const bf_multiply_histogram_entry *left;
    const bf_multiply_histogram_entry *right;

    left = lhs;
    right = rhs;
    if (left->term_count < right->term_count) {
        return -1;
    }
    if (left->term_count > right->term_count) {
        return 1;
    }
    return 0;
}

static int bf_compare_signature_entries(const void *lhs, const void *rhs) {
    const bf_multiply_signature_entry *left;
    const bf_multiply_signature_entry *right;

    left = lhs;
    right = rhs;
    if (left->occurrences > right->occurrences) {
        return -1;
    }
    if (left->occurrences < right->occurrences) {
        return 1;
    }
    return strcmp(left->signature, right->signature);
}

static int bf_compare_simple_segment_signature_entries(const void *lhs,
                                                       const void *rhs) {
    const bf_simple_segment_signature_entry *left;
    const bf_simple_segment_signature_entry *right;

    left = lhs;
    right = rhs;
    if (left->occurrences > right->occurrences) {
        return -1;
    }
    if (left->occurrences < right->occurrences) {
        return 1;
    }
    return strcmp(left->signature, right->signature);
}

static int bf_compare_runtime_simple_segment_entries(const void *lhs,
                                                     const void *rhs) {
    const bf_runtime_simple_segment_entry *left;
    const bf_runtime_simple_segment_entry *right;

    left = lhs;
    right = rhs;
    if (left->executions > right->executions) {
        return -1;
    }
    if (left->executions < right->executions) {
        return 1;
    }
    if (strcmp(left->signature, right->signature) != 0) {
        return strcmp(left->signature, right->signature);
    }
    if (left->context_signature == NULL && right->context_signature != NULL) {
        return -1;
    }
    if (left->context_signature != NULL && right->context_signature == NULL) {
        return 1;
    }
    if (left->context_signature == NULL && right->context_signature == NULL) {
        return 0;
    }
    return strcmp(left->context_signature, right->context_signature);
}

static int bf_compare_runtime_scan_context_entries(const void *lhs,
                                                   const void *rhs) {
    const bf_runtime_scan_context_entry *left;
    const bf_runtime_scan_context_entry *right;

    left = lhs;
    right = rhs;
    if (left->executions > right->executions) {
        return -1;
    }
    if (left->executions < right->executions) {
        return 1;
    }
    if (left->pending_offset < right->pending_offset) {
        return -1;
    }
    if (left->pending_offset > right->pending_offset) {
        return 1;
    }
    return left->step - right->step;
}

static void bf_dump_multiply_stats(const bf_program *program,
                                   const char *program_path) {
    bf_multiply_stats stats;
    size_t index;
    size_t preview_count;

    memset(&stats, 0, sizeof(stats));
    if (!bf_collect_multiply_stats_block(&program->root, &stats)) {
        fprintf(stderr, "failed to collect multiply_loop stats\n");
        bf_multiply_stats_dispose(&stats);
        return;
    }

    qsort(stats.histogram, stats.histogram_count, sizeof(*stats.histogram),
          bf_compare_histogram_entries);
    qsort(stats.signatures, stats.signature_count, sizeof(*stats.signatures),
          bf_compare_signature_entries);

    printf("multiply_loop stats for %s\n", program_path);
    printf("total_loops: %zu\n", stats.total_loops);
    printf("total_terms: %zu\n", stats.total_terms);
    printf("max_term_count: %zu\n", stats.max_term_count);
    if (stats.total_loops != 0) {
        printf("avg_terms: %.2f\n",
               (double)stats.total_terms / (double)stats.total_loops);
    }

    puts("term_count histogram:");
    for (index = 0; index < stats.histogram_count; ++index) {
        printf("  %zu terms: %zu\n", stats.histogram[index].term_count,
               stats.histogram[index].occurrences);
    }

    puts("top signatures:");
    preview_count = stats.signature_count < 12 ? stats.signature_count : 12;
    for (index = 0; index < preview_count; ++index) {
        printf("  %zu x %s\n", stats.signatures[index].occurrences,
               stats.signatures[index].signature);
    }

    bf_multiply_stats_dispose(&stats);
}

static void bf_dump_simple_segment_stats(const bf_program *program,
                                         const char *program_path) {
    bf_simple_segment_stats stats;
    size_t index;
    size_t preview_count;

    memset(&stats, 0, sizeof(stats));
    if (!bf_collect_simple_segment_stats_block(&program->root, &stats)) {
        fprintf(stderr, "failed to collect simple segment stats\n");
        bf_simple_segment_stats_dispose(&stats);
        return;
    }

    qsort(stats.signatures, stats.signature_count, sizeof(*stats.signatures),
          bf_compare_simple_segment_signature_entries);

    printf("simple segment stats for %s\n", program_path);
    printf("total_segments: %zu\n", stats.total_segments);
    printf("total_nodes: %zu\n", stats.total_nodes);
    printf("max_nodes: %zu\n", stats.max_nodes);
    if (stats.total_segments != 0) {
        printf("avg_nodes: %.2f\n",
               (double)stats.total_nodes / (double)stats.total_segments);
    }

    puts("top signatures:");
    preview_count = stats.signature_count < 20 ? stats.signature_count : 20;
    for (index = 0; index < preview_count; ++index) {
        printf("  %zu x %s\n", stats.signatures[index].occurrences,
               stats.signatures[index].signature);
    }

    bf_simple_segment_stats_dispose(&stats);
}

static int bf_compare_profile_entries(const void *lhs, const void *rhs) {
    const bf_profile_entry *left;
    const bf_profile_entry *right;

    left = lhs;
    right = rhs;
    if (left->count > right->count) {
        return -1;
    }
    if (left->count < right->count) {
        return 1;
    }
    return (int)left->kind - (int)right->kind;
}

static void bf_dump_runtime_profile(const bf_runtime_profile *profile,
                                    const char *program_path) {
    bf_profile_entry entries[BF_IR_NONNULL_MULTIPLY_LOOP + 1];
    size_t entry_count;
    size_t index;
    size_t preview_count;

    entry_count = 0;
    for (index = 0; index <= BF_IR_NONNULL_MULTIPLY_LOOP; ++index) {
        if (profile->node_counts[index] == 0) {
            continue;
        }
        entries[entry_count].kind = (bf_ir_kind)index;
        entries[entry_count].count = profile->node_counts[index];
        entry_count += 1;
    }

    qsort(entries, entry_count, sizeof(*entries), bf_compare_profile_entries);

    fprintf(stderr, "ir execution profile for %s\n", program_path);
    fprintf(stderr, "total_node_executions: %zu\n",
            profile->total_node_executions);
    if (profile->node_counts[BF_IR_SCAN] != 0) {
        fprintf(stderr,
                "scan_breakdown: step1=%zu step4=%zu other=%zu other_pos=%zu "
                "other_neg=%zu\n",
                profile->scan_step1_count, profile->scan_step4_count,
                profile->scan_other_count, profile->scan_other_positive_count,
                profile->scan_other_negative_count);
        if (profile->scan_step1_count != 0) {
            fprintf(stderr, "scan_avg_distance_step1: %.2f\n",
                    (double)profile->scan_step1_distance_total /
                        (double)profile->scan_step1_count);
        }
        if (profile->scan_step4_count != 0) {
            fprintf(stderr, "scan_avg_distance_step4: %.2f\n",
                    (double)profile->scan_step4_distance_total /
                        (double)profile->scan_step4_count);
        }
        if (profile->scan_other_count != 0) {
            fprintf(stderr, "scan_avg_distance_other: %.2f\n",
                    (double)profile->scan_other_distance_total /
                        (double)profile->scan_other_count);
        }
        if (profile->scan_other_positive_count != 0) {
            fprintf(stderr, "scan_avg_distance_other_pos: %.2f\n",
                    (double)profile->scan_other_positive_distance_total /
                        (double)profile->scan_other_positive_count);
        }
        if (profile->scan_other_negative_count != 0) {
            fprintf(stderr, "scan_avg_distance_other_neg: %.2f\n",
                    (double)profile->scan_other_negative_distance_total /
                        (double)profile->scan_other_negative_count);
        }
        fprintf(stderr, "scan_pending_offset_nonzero: %zu\n",
                profile->scan_pending_offset_nonzero_count);
        if (profile->scan_pending_offset_nonzero_count != 0) {
            fprintf(stderr, "scan_pending_offset_avg_abs: %.2f\n",
                    (double)profile->scan_pending_offset_abs_total /
                        (double)profile->scan_pending_offset_nonzero_count);
            fprintf(stderr, "scan_pending_offset_max_abs: %zu\n",
                    profile->scan_pending_offset_max_abs);
        }
    }
    if (profile->node_counts[BF_IR_MULTIPLY_LOOP] != 0 ||
        profile->node_counts[BF_IR_NONNULL_MULTIPLY_LOOP] != 0) {
        size_t multiply_count;

        multiply_count = profile->node_counts[BF_IR_MULTIPLY_LOOP] +
                         profile->node_counts[BF_IR_NONNULL_MULTIPLY_LOOP];
        fprintf(stderr, "multiply_loop_avg_terms: %.2f\n",
                (double)profile->multiply_loop_term_total /
                    (double)multiply_count);
    }

    for (index = 0; index < entry_count; ++index) {
        fprintf(stderr, "  %s: %zu", bf_ir_kind_name(entries[index].kind),
                entries[index].count);
        if (profile->total_node_executions != 0) {
            fprintf(stderr, " (%.2f%%)",
                    (double)entries[index].count * 100.0 /
                        (double)profile->total_node_executions);
        }
        fputc('\n', stderr);
    }

    if (profile->simple_segment_entry_count != 0) {
        qsort(profile->simple_segment_entries,
              profile->simple_segment_entry_count,
              sizeof(*profile->simple_segment_entries),
              bf_compare_runtime_simple_segment_entries);
        fprintf(stderr, "simple_segment_executions: %zu\n",
                profile->simple_segment_executions);
        fprintf(stderr, "simple_segment_total_nodes: %zu\n",
                profile->simple_segment_total_nodes);
        fprintf(stderr, "simple_segment_max_nodes: %zu\n",
                profile->simple_segment_max_nodes);
        if (profile->simple_segment_executions != 0) {
            fprintf(stderr, "simple_segment_avg_nodes: %.2f\n",
                    (double)profile->simple_segment_total_nodes /
                        (double)profile->simple_segment_executions);
        }
        fputs("top runtime simple segments:\n", stderr);
        preview_count = profile->simple_segment_entry_count < 20
                            ? profile->simple_segment_entry_count
                            : 20;
        for (index = 0; index < preview_count; ++index) {
            fprintf(stderr, "  %zu x %s",
                    profile->simple_segment_entries[index].executions,
                    profile->simple_segment_entries[index].signature);
            if (profile->simple_segment_entries[index].context_signature !=
                NULL) {
                fprintf(
                    stderr, " <= %s[%s]",
                    profile->simple_segment_entries[index].context_node == NULL
                        ? "R"
                        : (profile->simple_segment_entries[index]
                                       .context_kind == BF_IR_IF
                               ? "F"
                               : (profile->simple_segment_entries[index]
                                              .context_kind == BF_IR_LOOP
                                      ? "L"
                                      : "R")),
                    profile->simple_segment_entries[index].context_signature);
            }
            fputc('\n', stderr);
        }
    }

    if (profile->scan_context_entry_count != 0) {
        qsort(profile->scan_context_entries, profile->scan_context_entry_count,
              sizeof(*profile->scan_context_entries),
              bf_compare_runtime_scan_context_entries);
        fputs("top runtime scan contexts:\n", stderr);
        preview_count = profile->scan_context_entry_count < 20
                            ? profile->scan_context_entry_count
                            : 20;
        for (index = 0; index < preview_count; ++index) {
            fprintf(stderr, "  %zu x P%d,S%d\n",
                    profile->scan_context_entries[index].executions,
                    profile->scan_context_entries[index].pending_offset,
                    profile->scan_context_entries[index].step);
        }
    }
}

int main(int argc, char **argv) {
    static const size_t tape_size = 30000;
    const char *program_path;
    const char *dump_jit_path;
    int dump_multiply_stats;
    int dump_simple_segment_stats;
    int dump_control_flow_stats;
    int dump_jit;
    int profile_ir_execution;
    bf_program program;
    bf_parse_err parse_err;
    bf_jit_err jit_err;
    bf_runtime_profile runtime_profile;
    uint8_t *tape;
    char *src;
    size_t src_length;
    int exit_code;
    int runtime_result;

    dump_multiply_stats = 0;
    dump_simple_segment_stats = 0;
    dump_control_flow_stats = 0;
    dump_jit = 0;
    profile_ir_execution = 0;
    program_path = NULL;
    dump_jit_path = NULL;

    if (argc == 2) {
        program_path = argv[1];
    } else if (argc == 3 && strcmp(argv[1], "--dump-multiply-stats") == 0) {
        dump_multiply_stats = 1;
        program_path = argv[2];
    } else if (argc == 3 &&
               strcmp(argv[1], "--dump-simple-segment-stats") == 0) {
        dump_simple_segment_stats = 1;
        program_path = argv[2];
    } else if (argc == 3 && strcmp(argv[1], "--dump-control-flow-stats") == 0) {
        dump_control_flow_stats = 1;
        program_path = argv[2];
    } else if (argc == 4 && strcmp(argv[1], "--dump-jit") == 0) {
        dump_jit = 1;
        program_path = argv[2];
        dump_jit_path = argv[3];
    } else if (argc == 3 && strcmp(argv[1], "--profile-ir-execution") == 0) {
        profile_ir_execution = 1;
        program_path = argv[2];
    } else {
        fprintf(stderr,
                "usage: %s "
                "[--dump-multiply-stats|--dump-simple-segment-stats|--dump-"
                "control-flow-stats|--profile-ir-execution] <program.bf>\n"
                "       %s --dump-jit <program.bf> <output.bin>\n",
                argv[0], argv[0]);
        return 1;
    }

    if (!bf_read_file(program_path, &src, &src_length)) {
        fprintf(stderr, "failed to read %s\n", program_path);
        return 1;
    }

    if (!bf_parse_src(src, src_length, &program, &parse_err)) {
        fprintf(stderr, "parse err at %zu:%zu: %s\n", parse_err.loc.line,
                parse_err.loc.column, parse_err.msg);
        free(src);
        return 1;
    }

    if (dump_multiply_stats) {
        bf_opt_program(&program);
        bf_dump_multiply_stats(&program, program_path);
        bf_program_dispose(&program);
        free(src);
        return 0;
    }

    if (dump_simple_segment_stats) {
        bf_opt_program(&program);
        bf_dump_simple_segment_stats(&program, program_path);
        bf_program_dispose(&program);
        free(src);
        return 0;
    }

    if (dump_control_flow_stats) {
        bf_dump_control_flow_stats(&program, program_path, "pre-opt");
        bf_opt_program(&program);
        bf_dump_control_flow_stats(&program, program_path, "post-opt");
        bf_program_dispose(&program);
        free(src);
        return 0;
    }

    if (dump_jit) {
        bf_opt_program(&program);
        if (!bf_jit_dump_program_code(&program, dump_jit_path, &jit_err)) {
            fprintf(stderr, "jit err: %s\n", jit_err.msg);
            bf_program_dispose(&program);
            free(src);
            return 1;
        }
        bf_program_dispose(&program);
        free(src);
        return 0;
    }

    bf_opt_program(&program);

    tape = calloc(tape_size, sizeof(*tape));
    if (tape == NULL) {
        fprintf(stderr, "failed to allocate tape\n");
        bf_program_dispose(&program);
        free(src);
        return 1;
    }

    exit_code = 0;
    if (profile_ir_execution) {
        flockfile(stdout);
        flockfile(stdin);
        runtime_result = bf_runtime_execute_profiled(&program, tape, tape_size,
                                                     &runtime_profile);
        funlockfile(stdin);
        funlockfile(stdout);
        if (runtime_result < 0) {
            fprintf(stderr, "runtime err: %d\n", runtime_result);
            exit_code = 1;
        } else {
            bf_dump_runtime_profile(&runtime_profile, program_path);
        }
        bf_runtime_profile_dispose(&runtime_profile);
    } else if (!bf_jit_execute_program(&program, tape, tape_size, &jit_err)) {
        fprintf(stderr, "jit err: %s\n", jit_err.msg);
        exit_code = 1;
    }

    free(tape);
    bf_program_dispose(&program);
    free(src);
    return exit_code;
}
