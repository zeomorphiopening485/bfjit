#include "bfopt.h"

#include <stdlib.h>
#include <string.h>

static void bf_opt_set_zero(bf_ir_node *node) {
    const bf_ir_block *body;

    if (node->kind != BF_IR_LOOP || node->body.count != 1) {
        return;
    }

    body = &node->body;

    /* [-] or [+]: ループ消去 */
    if (body->nodes[0].kind == BF_IR_ADD_DATA &&
        (body->nodes[0].arg == -1 || body->nodes[0].arg == 1)) {
        bf_ir_block_dispose(&node->body);
        node->kind = BF_IR_SET_ZERO;
        node->arg = 0;
        return;
    }

    /* [>] or [<] or [>>>] etc: ループ解析 */
    if (body->nodes[0].kind == BF_IR_ADD_PTR) {
        int step = body->nodes[0].arg;
        bf_ir_block_dispose(&node->body);
        node->kind = BF_IR_SCAN;
        node->arg = step;
        return;
    }
}

/*
 * 乗算/コピー ループパターンの検出を試行
 *
 * 乗算ループは [->+++>++<<] のような形をしており, ループ本体は ADD_PTR および
 * ADD_DATA のみで構成され, ポインタはオフセット 0 に戻りオフセット 0 はちょうど
 * 1 だけデクリメント (または 1 だけインクリメント,
 * これはラップアラウンドで動作) される
 *
 * 成功すると LOOP は MULTIPLY_LOOP に置き換えられ、terms 配列に各影響セルの
 * {offset, factor} ペアが格納される
 */
#define BF_MULTIPLY_MAX_OFFSETS 256

static void bf_try_recognize_multiply_loop(bf_ir_node *node) {
    const bf_ir_block *body;
    size_t i;
    int current_offset;
    int ptr_sum;
    int origin_delta;
    int sign;

    /* オフセット -> 累積デルタ */
    int offsets[BF_MULTIPLY_MAX_OFFSETS];
    int offset_keys[BF_MULTIPLY_MAX_OFFSETS];
    size_t offset_count;

    bf_multiply_term *terms;
    size_t term_count;

    if (node->kind != BF_IR_LOOP) {
        return;
    }

    body = &node->body;

    /* 1. body には ADD_PTR と ADD_DATA のみを含める */
    for (i = 0; i < body->count; ++i) {
        if (body->nodes[i].kind != BF_IR_ADD_PTR &&
            body->nodes[i].kind != BF_IR_ADD_DATA) {
            return;
        }
    }

    /* 2. body を走査しポインタのオフセットを追跡, delta を累積 */
    current_offset = 0;
    ptr_sum = 0;
    offset_count = 0;

    for (i = 0; i < body->count; ++i) {
        if (body->nodes[i].kind == BF_IR_ADD_PTR) {
            current_offset += body->nodes[i].arg;
            ptr_sum += body->nodes[i].arg;
        } else {
            /* current_offset で ADD_DATA */
            size_t j;
            int found = 0;

            for (j = 0; j < offset_count; ++j) {
                if (offset_keys[j] == current_offset) {
                    offsets[j] += body->nodes[i].arg;
                    found = 1;
                    break;
                }
            }

            if (!found) {
                if (offset_count >= BF_MULTIPLY_MAX_OFFSETS) {
                    return;
                }
                offset_keys[offset_count] = current_offset;
                offsets[offset_count] = body->nodes[i].arg;
                offset_count += 1;
            }
        }
    }

    /* 3. ポインタはオフセット 0 に戻る */
    if (ptr_sum != 0) {
        return;
    }

    /* 4. オフセット 0 は -1 または +1 の delta を持つ */
    origin_delta = 0;
    for (i = 0; i < offset_count; ++i) {
        if (offset_keys[i] == 0) {
            origin_delta = offsets[i];
            break;
        }
    }

    if (origin_delta != -1 && origin_delta != 1) {
        return;
    }

    /*
     * 5. terms 配列を構築
     * origin_delta が +1 の場合, すべての係数を反転させてセマンティクスを
     * cell[off] += cell[0] * factor (cell[0] は 0 にデクリメントされる) にする
     */
    sign = (origin_delta == -1) ? 1 : -1;

    term_count = 0;
    for (i = 0; i < offset_count; ++i) {
        if (offset_keys[i] != 0) {
            term_count += 1;
        }
    }

    terms = NULL;
    if (term_count > 0) {
        terms = malloc(term_count * sizeof(*terms));
        if (terms == NULL) {
            return;
        }

        term_count = 0;
        for (i = 0; i < offset_count; ++i) {
            if (offset_keys[i] != 0) {
                terms[term_count].offset = offset_keys[i];
                terms[term_count].factor = offsets[i] * sign;
                term_count += 1;
            }
        }
    }

    /* 6. ノードを変換 */
    bf_ir_block_dispose(&node->body);
    node->kind = BF_IR_MULTIPLY_LOOP;
    node->arg = 0;
    node->terms = terms;
    node->term_count = term_count;
}

static int bf_set_node_offset(const bf_ir_node *node) {
    switch (node->kind) {
    case BF_IR_SET_ZERO:
    case BF_IR_SET_CONST:
        return 0;
    case BF_IR_SET_CONST_OFFSET:
        return node->offset;
    default:
        return 0;
    }
}

static int bf_add_node_offset(const bf_ir_node *node) {
    switch (node->kind) {
    case BF_IR_ADD_DATA:
        return 0;
    case BF_IR_ADD_DATA_OFFSET:
        return node->offset;
    default:
        return 0;
    }
}

static void bf_opt_fold_set_const(bf_ir_block *block) {
    size_t index;

    for (index = 0; index + 1 < block->count; ++index) {
        bf_ir_node *node;
        bf_ir_node *next;

        node = &block->nodes[index];
        next = &block->nodes[index + 1];

        if ((node->kind == BF_IR_SET_ZERO || node->kind == BF_IR_SET_CONST ||
             node->kind == BF_IR_SET_CONST_OFFSET) &&
            (next->kind == BF_IR_ADD_DATA ||
             next->kind == BF_IR_ADD_DATA_OFFSET) &&
            bf_set_node_offset(node) == bf_add_node_offset(next)) {
            int merged_value;

            merged_value =
                ((node->kind == BF_IR_SET_ZERO) ? 0 : node->arg) + next->arg;
            node->arg = merged_value;
            if (bf_set_node_offset(node) == 0) {
                node->kind =
                    (merged_value == 0) ? BF_IR_SET_ZERO : BF_IR_SET_CONST;
            } else {
                node->kind = BF_IR_SET_CONST_OFFSET;
            }
            memmove(&block->nodes[index + 1], &block->nodes[index + 2],
                    (block->count - index - 2) * sizeof(*block->nodes));
            block->count -= 1;
            index -= (index > 0);
        }
    }
}

typedef struct bf_store_record {
    int offset;
    size_t node_index;
} bf_store_record;

static size_t bf_find_store_record(const bf_store_record *records,
                                   size_t record_count, int offset) {
    size_t index;

    for (index = 0; index < record_count; ++index) {
        if (records[index].offset == offset) {
            return index;
        }
    }

    return record_count;
}

static void bf_drop_store_record(bf_store_record *records, size_t *record_count,
                                 int offset) {
    size_t record_index;

    record_index = bf_find_store_record(records, *record_count, offset);
    if (record_index == *record_count) {
        return;
    }

    memmove(&records[record_index], &records[record_index + 1],
            (*record_count - record_index - 1) * sizeof(*records));
    *record_count -= 1;
}

static void bf_kill_prior_store(bf_store_record *records, size_t *record_count,
                                int offset, unsigned char *remove_mask) {
    size_t record_index;

    record_index = bf_find_store_record(records, *record_count, offset);
    if (record_index == *record_count) {
        return;
    }

    remove_mask[records[record_index].node_index] = 1;
    memmove(&records[record_index], &records[record_index + 1],
            (*record_count - record_index - 1) * sizeof(*records));
    *record_count -= 1;
}

static void bf_record_store(bf_store_record *records, size_t *record_count,
                            int offset, size_t node_index,
                            unsigned char *remove_mask) {
    size_t record_index;

    record_index = bf_find_store_record(records, *record_count, offset);
    if (record_index < *record_count) {
        remove_mask[records[record_index].node_index] = 1;
        records[record_index].node_index = node_index;
        return;
    }

    records[*record_count].offset = offset;
    records[*record_count].node_index = node_index;
    *record_count += 1;
}

static void bf_clear_store_records(size_t *record_count) { *record_count = 0; }

static void bf_opt_eliminate_dead_stores(bf_ir_block *block) {
    bf_store_record *records;
    unsigned char *remove_mask;
    size_t record_count;
    size_t index;
    size_t write_index;
    int current_offset;
    int changed;

    if (block->count < 2) {
        return;
    }

    records = malloc(block->count * sizeof(*records));
    remove_mask = calloc(block->count, sizeof(*remove_mask));
    if (records == NULL || remove_mask == NULL) {
        free(records);
        free(remove_mask);
        return;
    }

    record_count = 0;
    current_offset = 0;
    changed = 0;

    for (index = 0; index < block->count; ++index) {
        bf_ir_node *node;

        node = &block->nodes[index];
        switch (node->kind) {
        case BF_IR_ADD_PTR:
            current_offset += node->arg;
            break;
        case BF_IR_SET_ZERO:
        case BF_IR_SET_CONST:
            bf_record_store(records, &record_count, current_offset, index,
                            remove_mask);
            break;
        case BF_IR_SET_CONST_OFFSET:
            bf_record_store(records, &record_count,
                            current_offset + node->offset, index, remove_mask);
            break;
        case BF_IR_INPUT:
            bf_kill_prior_store(records, &record_count, current_offset,
                                remove_mask);
            break;
        case BF_IR_ADD_DATA:
        case BF_IR_OUTPUT:
            bf_drop_store_record(records, &record_count, current_offset);
            break;
        case BF_IR_ADD_DATA_OFFSET:
            bf_drop_store_record(records, &record_count,
                                 current_offset + node->offset);
            break;
        case BF_IR_MULTI_ZERO: {
            size_t term_index;

            for (term_index = 0; term_index < node->term_count; ++term_index) {
                bf_kill_prior_store(records, &record_count,
                                    current_offset +
                                        node->terms[term_index].offset,
                                    remove_mask);
            }
            current_offset += node->arg;
            break;
        }
        case BF_IR_LOOP:
        case BF_IR_IF:
        case BF_IR_SCAN:
        case BF_IR_MULTIPLY_LOOP:
        case BF_IR_NONNULL_MULTIPLY_LOOP:
            bf_clear_store_records(&record_count);
            break;
        default:
            bf_clear_store_records(&record_count);
            break;
        }
    }

    for (index = 0; index < block->count; ++index) {
        if (remove_mask[index] != 0) {
            changed = 1;
            break;
        }
    }

    if (changed) {
        write_index = 0;
        for (index = 0; index < block->count; ++index) {
            if (remove_mask[index] == 0) {
                if (write_index != index) {
                    block->nodes[write_index] = block->nodes[index];
                }
                write_index += 1;
            }
        }
        block->count = write_index;
    }

    free(records);
    free(remove_mask);
}

static void bf_try_fold_multi_zero(bf_ir_block *block) {
    size_t index;

    for (index = 0; index < block->count; ++index) {
        size_t scan_index;
        size_t zero_count;
        int current_offset;
        bf_multiply_term *offsets;

        if (block->nodes[index].kind != BF_IR_SET_ZERO) {
            continue;
        }

        zero_count = 1;
        current_offset = 0;
        scan_index = index + 1;
        while (scan_index + 1 < block->count &&
               block->nodes[scan_index].kind == BF_IR_ADD_PTR &&
               block->nodes[scan_index + 1].kind == BF_IR_SET_ZERO) {
            current_offset += block->nodes[scan_index].arg;
            zero_count += 1;
            scan_index += 2;
        }

        if (zero_count < 2) {
            continue;
        }

        offsets = malloc(zero_count * sizeof(*offsets));
        if (offsets == NULL) {
            continue;
        }

        offsets[0].offset = 0;
        offsets[0].factor = 0;
        current_offset = 0;
        zero_count = 1;
        scan_index = index + 1;
        while (scan_index + 1 < block->count &&
               block->nodes[scan_index].kind == BF_IR_ADD_PTR &&
               block->nodes[scan_index + 1].kind == BF_IR_SET_ZERO) {
            current_offset += block->nodes[scan_index].arg;
            offsets[zero_count].offset = current_offset;
            offsets[zero_count].factor = 0;
            zero_count += 1;
            scan_index += 2;
        }

        if (scan_index < block->count &&
            block->nodes[scan_index].kind == BF_IR_ADD_PTR) {
            current_offset += block->nodes[scan_index].arg;
            scan_index += 1;
        }

        block->nodes[index].kind = BF_IR_MULTI_ZERO;
        block->nodes[index].arg = current_offset;
        block->nodes[index].terms = offsets;
        block->nodes[index].term_count = zero_count;

        memmove(&block->nodes[index + 1], &block->nodes[scan_index],
                (block->count - scan_index) * sizeof(*block->nodes));
        block->count -= (scan_index - index - 1);
    }
}

static void bf_try_recognize_zeroing_loop(bf_ir_node *node) {
    const bf_ir_block *body;
    bf_multiply_term *terms;
    int *zero_offsets;
    size_t zero_count;
    size_t index;
    int current_offset;
    int ptr_sum;
    int origin_delta;

    if (node->kind != BF_IR_LOOP) {
        return;
    }

    body = &node->body;
    if (body->count < 2) {
        return;
    }

    zero_offsets = malloc(body->count * sizeof(*zero_offsets));
    if (zero_offsets == NULL) {
        return;
    }

    zero_count = 0;
    current_offset = 0;
    ptr_sum = 0;
    origin_delta = 0;

    for (index = 0; index < body->count; ++index) {
        const bf_ir_node *body_node;

        body_node = &body->nodes[index];
        switch (body_node->kind) {
        case BF_IR_ADD_PTR:
            if (body_node->arg == 0) {
                free(zero_offsets);
                return;
            }
            current_offset += body_node->arg;
            ptr_sum += body_node->arg;
            break;
        case BF_IR_SET_ZERO:
        case BF_IR_SET_CONST:
            if (body_node->kind == BF_IR_SET_CONST && body_node->arg != 0) {
                free(zero_offsets);
                return;
            }
            if (current_offset == 0) {
                free(zero_offsets);
                return;
            }
            {
                size_t zero_index;
                int found;

                found = 0;
                for (zero_index = 0; zero_index < zero_count; ++zero_index) {
                    if (zero_offsets[zero_index] == current_offset) {
                        found = 1;
                        break;
                    }
                }
                if (!found) {
                    zero_offsets[zero_count] = current_offset;
                    zero_count += 1;
                }
            }
            break;
        case BF_IR_ADD_DATA:
            if (current_offset != 0) {
                free(zero_offsets);
                return;
            }
            origin_delta += body_node->arg;
            break;
        default:
            free(zero_offsets);
            return;
        }
    }

    if (ptr_sum != 0 || zero_count == 0 ||
        (origin_delta != -1 && origin_delta != 1)) {
        free(zero_offsets);
        return;
    }

    terms = malloc((zero_count + 1) * sizeof(*terms));
    if (terms == NULL) {
        free(zero_offsets);
        return;
    }

    terms[0].offset = 0;
    terms[0].factor = 0;
    for (index = 0; index < zero_count; ++index) {
        terms[index + 1].offset = zero_offsets[index];
        terms[index + 1].factor = 0;
    }

    free(zero_offsets);

    node->body.nodes[0].kind = BF_IR_MULTI_ZERO;
    node->body.nodes[0].arg = 0;
    node->body.nodes[0].terms = terms;
    node->body.nodes[0].term_count = zero_count + 1;
    node->body.count = 1;
}

static void bf_opt_fold_redundant_scan_return(bf_ir_block *block) {
    size_t index;

    for (index = 0; index + 2 < block->count; ++index) {
        bf_ir_node *first;
        bf_ir_node *move;
        bf_ir_node *second;

        first = &block->nodes[index];
        move = &block->nodes[index + 1];
        second = &block->nodes[index + 2];

        if (first->kind != BF_IR_SCAN || move->kind != BF_IR_ADD_PTR ||
            second->kind != BF_IR_SCAN) {
            continue;
        }

        if (first->arg == 0 || second->arg != -first->arg ||
            move->arg != -first->arg) {
            continue;
        }

        memmove(&block->nodes[index], &block->nodes[index + 1],
                (block->count - index - 1) * sizeof(*block->nodes));
        block->count -= 1;
        index -= (index > 0);
    }
}

static void bf_fold_offset_cell_ops(bf_ir_block *block) {
    size_t index;

    if (block->count < 3) {
        return;
    }

    for (index = 0; index + 2 < block->count; ++index) {
        bf_ir_node *first;
        bf_ir_node *second;
        bf_ir_node *third;

        first = &block->nodes[index];
        second = &block->nodes[index + 1];
        third = &block->nodes[index + 2];

        if (first->kind != BF_IR_ADD_PTR || third->kind != BF_IR_ADD_PTR ||
            first->arg == 0 || third->arg != -first->arg) {
            continue;
        }

        if (second->kind != BF_IR_ADD_DATA && second->kind != BF_IR_SET_ZERO &&
            second->kind != BF_IR_SET_CONST) {
            continue;
        }

        second->offset = first->arg;
        if (second->kind == BF_IR_ADD_DATA) {
            second->kind = BF_IR_ADD_DATA_OFFSET;
        } else if (second->kind == BF_IR_SET_ZERO) {
            second->kind = BF_IR_SET_CONST_OFFSET;
            second->arg = 0;
        } else {
            second->kind = BF_IR_SET_CONST_OFFSET;
        }

        memmove(&block->nodes[index], &block->nodes[index + 1],
                (block->count - index - 1) * sizeof(*block->nodes));
        block->count -= 1;
        memmove(&block->nodes[index + 1], &block->nodes[index + 2],
                (block->count - index - 1) * sizeof(*block->nodes));
        block->count -= 1;

        index -= (index > 0);
    }
}

static int bf_multi_zero_touches_origin(const bf_ir_node *node,
                                        int current_offset) {
    size_t term_index;

    for (term_index = 0; term_index < node->term_count; ++term_index) {
        if (current_offset + node->terms[term_index].offset == 0) {
            return 1;
        }
    }

    return 0;
}

static int bf_multiply_loop_may_touch_origin(const bf_ir_node *node,
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

static void bf_mark_known_nonnull_multiply_in_ifs(bf_ir_block *block) {
    size_t index;

    for (index = 0; index < block->count; ++index) {
        bf_ir_node *node;

        node = &block->nodes[index];
        if (node->kind == BF_IR_IF && node->body.count != 0 &&
            node->body.nodes[0].kind == BF_IR_MULTIPLY_LOOP) {
            node->body.nodes[0].kind = BF_IR_NONNULL_MULTIPLY_LOOP;
        }
        if (node->kind == BF_IR_LOOP || node->kind == BF_IR_IF) {
            bf_mark_known_nonnull_multiply_in_ifs(&node->body);
        }
    }
}

static int bf_try_convert_loop_to_if(bf_ir_node *node) {
    int current_offset;
    int origin_zero;
    size_t index;

    if (node->kind != BF_IR_LOOP) {
        return 0;
    }

    current_offset = 0;
    origin_zero = 0;

    for (index = 0; index < node->body.count; ++index) {
        bf_ir_node *body_node;

        body_node = &node->body.nodes[index];
        switch (body_node->kind) {
        case BF_IR_ADD_PTR:
            current_offset += body_node->arg;
            break;
        case BF_IR_SET_ZERO:
            if (current_offset == 0) {
                origin_zero = 1;
            }
            break;
        case BF_IR_SET_CONST:
            if (current_offset == 0) {
                if (body_node->arg == 0) {
                    origin_zero = 1;
                } else {
                    origin_zero = 0;
                }
            }
            break;
        case BF_IR_SET_CONST_OFFSET:
            if (current_offset + body_node->offset == 0) {
                if (body_node->arg == 0) {
                    origin_zero = 1;
                } else {
                    origin_zero = 0;
                }
            }
            break;
        case BF_IR_ADD_DATA:
        case BF_IR_INPUT:
            if (current_offset == 0) {
                return 0;
            }
            break;
        case BF_IR_ADD_DATA_OFFSET:
            if (current_offset + body_node->offset == 0) {
                return 0;
            }
            break;
        case BF_IR_OUTPUT:
            break;
        case BF_IR_SCAN:
        case BF_IR_LOOP:
        case BF_IR_IF:
            return 0;
        case BF_IR_MULTI_ZERO:
            if (bf_multi_zero_touches_origin(body_node, current_offset)) {
                origin_zero = 1;
            }
            current_offset += body_node->arg;
            break;
        case BF_IR_MULTIPLY_LOOP:
        case BF_IR_NONNULL_MULTIPLY_LOOP:
            if (bf_multiply_loop_may_touch_origin(body_node, current_offset)) {
                if (current_offset != 0) {
                    return 0;
                }
                origin_zero = 1;
            }
            break;
        default:
            return 0;
        }
    }

    if (current_offset != 0 || !origin_zero) {
        return 0;
    }

    node->kind = BF_IR_IF;
    return 1;
}

static void bf_opt_block(bf_ir_block *block) {
    size_t i;

    for (i = 0; i < block->count; ++i) {
        if (block->nodes[i].kind == BF_IR_LOOP) {
            bf_opt_block(&block->nodes[i].body);
            bf_opt_set_zero(&block->nodes[i]);
            bf_try_recognize_zeroing_loop(&block->nodes[i]);
            bf_try_recognize_multiply_loop(&block->nodes[i]);
        }
    }

    bf_opt_fold_set_const(block);
    bf_opt_eliminate_dead_stores(block);
#if defined(__aarch64__)
    bf_opt_fold_redundant_scan_return(block);
#endif
    bf_try_fold_multi_zero(block);
    bf_opt_eliminate_dead_stores(block);

    for (i = 0; i < block->count; ++i) {
        bf_try_convert_loop_to_if(&block->nodes[i]);
    }

    bf_opt_eliminate_dead_stores(block);
    bf_mark_known_nonnull_multiply_in_ifs(block);
}

void bf_opt_program(bf_program *program) {
    if (program == NULL) {
        return;
    }

    bf_opt_block(&program->root);
}
