#ifndef BFJIT_INTERNAL_H
#define BFJIT_INTERNAL_H

#include "bfjit.h"

typedef int (*bf_jit_entry_fn)(uint8_t *tape, size_t tape_size);
typedef int (*bf_runtime_entry_fn)(uint8_t *tape, size_t tape_size,
                                   const bf_program *program);

typedef struct bf_jit_state {
    uint8_t *tape;
    size_t tape_size;
    size_t pointer;
} bf_jit_state;

typedef struct bf_jit_compiled_program {
    bf_jit_entry_fn entry;
    void *code;
    size_t code_size;
    size_t mapping_size;
} bf_jit_compiled_program;

typedef struct bf_runtime_profile {
    size_t total_node_executions;
    size_t node_counts[BF_IR_NONNULL_MULTIPLY_LOOP + 1];
    size_t scan_step1_count;
    size_t scan_step4_count;
    size_t scan_other_count;
    size_t scan_other_positive_count;
    size_t scan_other_negative_count;
    size_t scan_step1_distance_total;
    size_t scan_step4_distance_total;
    size_t scan_other_distance_total;
    size_t scan_other_positive_distance_total;
    size_t scan_other_negative_distance_total;
    size_t scan_pending_offset_nonzero_count;
    size_t scan_pending_offset_abs_total;
    size_t scan_pending_offset_max_abs;
    struct bf_runtime_scan_context_entry *scan_context_entries;
    size_t scan_context_entry_count;
    size_t scan_context_entry_capacity;
    size_t multiply_loop_term_total;
    size_t simple_segment_executions;
    size_t simple_segment_total_nodes;
    size_t simple_segment_max_nodes;
    struct bf_runtime_simple_segment_entry *simple_segment_entries;
    size_t simple_segment_entry_count;
    size_t simple_segment_entry_capacity;
} bf_runtime_profile;

typedef struct bf_runtime_simple_segment_entry {
    char *signature;
    const bf_ir_node *context_node;
    char *context_signature;
    bf_ir_kind context_kind;
    size_t executions;
} bf_runtime_simple_segment_entry;

typedef struct bf_runtime_scan_context_entry {
    int pending_offset;
    int step;
    size_t executions;
} bf_runtime_scan_context_entry;

typedef enum bf_jit_patch_kind {
    BF_JIT_PATCH_BRANCH,
    BF_JIT_PATCH_COND,
    BF_JIT_PATCH_CBZ,
    BF_JIT_PATCH_CBNZ
} bf_jit_patch_kind;

typedef struct bf_jit_patch {
    size_t offset;
    bf_jit_patch_kind kind;
} bf_jit_patch;

typedef struct bf_jit_label {
    size_t position;
    bf_jit_patch *patches;
    size_t patch_count;
    size_t patch_capacity;
} bf_jit_label;

typedef enum bf_jit_simple_effect_kind {
    BF_JIT_SIMPLE_EFFECT_NONE = 0,
    BF_JIT_SIMPLE_EFFECT_ADD = 1,
    BF_JIT_SIMPLE_EFFECT_SET = 2
} bf_jit_simple_effect_kind;

typedef struct bf_jit_simple_effect {
    int effective_offset;
    bf_jit_simple_effect_kind kind;
    uint8_t value;
} bf_jit_simple_effect;

typedef struct bf_jit_two_simple_effects {
    size_t count;
    bf_jit_simple_effect effects[2];
} bf_jit_two_simple_effects;

typedef struct bf_jit_simple_run_info {
    size_t next_index;
    int pending_offset_after;
    int min_offset;
    int max_offset;
    bool has_simple;
    size_t first_simple_index;
    int first_simple_pending_offset;
    size_t second_simple_index;
    int second_simple_pending_offset;
    size_t simple_count;
} bf_jit_simple_run_info;

typedef struct bf_jit_pending_offset_ops {
    int (*emit_simple_run)(void *context, const bf_ir_block *block,
                           size_t start_index, size_t *next_index,
                           int *pending_offset);
    int (*emit_control_with_pending_offset)(void *context,
                                            const bf_ir_node *node,
                                            int pending_offset);
    int (*emit_input_at_offset)(void *context, int offset);
    int (*emit_output_at_offset)(void *context, int offset);
    int (*emit_add_ptr)(void *context, int delta);
    int (*emit_scan_with_pending_offset)(void *context, const bf_ir_node *node,
                                         int pending_offset);
    int (*emit_multiply_with_pending_offset)(void *context,
                                             const bf_ir_node *node,
                                             int pending_offset);
    int (*emit_node)(void *context, const bf_ir_node *node);
} bf_jit_pending_offset_ops;

typedef enum bf_jit_control_flow_plan_kind {
    BF_JIT_CONTROL_FLOW_PLAN_NONE = 0,
    BF_JIT_CONTROL_FLOW_PLAN_LOOP_WITH_PENDING_OFFSET,
    BF_JIT_CONTROL_FLOW_PLAN_IF_WITH_PENDING_OFFSET,
} bf_jit_control_flow_plan_kind;

typedef struct bf_jit_control_flow_plan {
    bf_jit_control_flow_plan_kind kind;
} bf_jit_control_flow_plan;

typedef enum bf_jit_scan_plan_kind {
    BF_JIT_SCAN_PLAN_ERROR = 0,
    BF_JIT_SCAN_PLAN_STEP1,
    BF_JIT_SCAN_PLAN_STRIDE4,
    BF_JIT_SCAN_PLAN_GENERIC,
} bf_jit_scan_plan_kind;

typedef struct bf_jit_scan_plan {
    bf_jit_scan_plan_kind kind;
    int step;
} bf_jit_scan_plan;

typedef struct bf_jit_scan_ops {
    void (*label_init)(bf_jit_label *label);
    void (*label_dispose)(bf_jit_label *label);
    int (*bind_label)(void *context, bf_jit_label *label);
    int (*emit_jump)(void *context, bf_jit_label *label);
    int (*emit_invalid_step)(void *context);
    int (*emit_load_state)(void *context);
    int (*emit_store_pointer)(void *context);
    int (*emit_prepare_upper_bound)(void *context);
    int (*emit_branch_current_zero)(void *context, bf_jit_label *label);
    int (*emit_branch_current_nonzero)(void *context, bf_jit_label *label);
    int (*emit_branch_disp_zero)(void *context, int offset,
                                 bf_jit_label *label);
    int (*emit_branch_if_current_oob)(void *context);
    int (*emit_branch_if_advance_oob)(void *context, int delta,
                                      bf_jit_label *label);
    int (*emit_branch_if_backward_oob)(void *context, int delta);
    int (*emit_advance)(void *context, int delta);
} bf_jit_scan_ops;

typedef struct bf_jit_multi_zero_plan {
    bool is_noop;
    int min_offset;
    int max_offset;
} bf_jit_multi_zero_plan;

typedef struct bf_jit_multiply_loop_plan {
    bool zero_current_only;
    bool has_terms;
    bool has_small_term_count;
    int min_offset;
    int max_offset;
} bf_jit_multiply_loop_plan;

typedef enum bf_jit_multiply_term_plan_kind {
    BF_JIT_MULTIPLY_TERM_PLAN_ADD_SOURCE = 0,
    BF_JIT_MULTIPLY_TERM_PLAN_SUB_SOURCE,
    BF_JIT_MULTIPLY_TERM_PLAN_GENERAL,
} bf_jit_multiply_term_plan_kind;

typedef struct bf_jit_multiply_term_plan {
    bf_jit_multiply_term_plan_kind kind;
    int offset;
    int factor;
} bf_jit_multiply_term_plan;

typedef struct bf_jit_multiply_term_ops {
    int (*emit_term)(void *context, const bf_jit_multiply_term_plan *plan);
} bf_jit_multiply_term_ops;

typedef struct bf_jit_size_hint_ops {
    size_t (*node_size_hint)(const bf_ir_node *node, void *context);
    void *context;
} bf_jit_size_hint_ops;

void bf_jit_err_reset(bf_jit_err *err);
void bf_set_jit_err(bf_jit_err *err, const char *msg);

bool bf_jit_backend_compile(const bf_program *program,
                            bf_jit_compiled_program *compiled, bf_jit_err *err);
void bf_jit_backend_dispose(bf_jit_compiled_program *compiled);

size_t bf_jit_arch_code_size(const bf_program *program);
bool bf_jit_arch_emit_program(uint8_t *code, size_t code_size,
                              const bf_program *program, bf_jit_err *err,
                              size_t *emitted_size);

bool bf_jit_node_is_simple(const bf_ir_node *node);
int bf_jit_simple_node_effective_offset(const bf_ir_node *node,
                                        int pending_offset);
bf_jit_simple_effect_kind
bf_jit_simple_node_effect_kind(const bf_ir_node *node);
uint8_t bf_jit_simple_node_effect_value(const bf_ir_node *node);
void bf_jit_merge_simple_effect(bf_jit_simple_effect_kind *effect_kind,
                                uint8_t *effect_value,
                                bf_jit_simple_effect_kind next_kind,
                                uint8_t next_value);
void bf_jit_collect_simple_run_info(const bf_ir_block *block,
                                    size_t start_index, int pending_offset,
                                    bf_jit_simple_run_info *info);
bool bf_jit_if_has_nonnull_multiply_simple_tail(
    const bf_ir_node *node, bf_jit_simple_run_info *tail_info);
void bf_jit_build_two_simple_effects(const bf_ir_node *first_node,
                                     int first_pending_offset,
                                     const bf_ir_node *second_node,
                                     int second_pending_offset,
                                     bf_jit_two_simple_effects *effects);
bool bf_jit_block_is_offset_safe_zero_delta(const bf_ir_block *block);
void bf_jit_build_control_flow_plan(const bf_ir_node *node, int pending_offset,
                                    bf_jit_control_flow_plan *plan);
void bf_jit_build_scan_plan(int step, bf_jit_scan_plan *plan);
int bf_jit_emit_scan_shared(int step, const bf_jit_scan_ops *ops,
                            void *context);
void bf_jit_build_multi_zero_plan(const bf_ir_node *node,
                                  bf_jit_multi_zero_plan *plan);
void bf_jit_build_multiply_loop_plan(const bf_ir_node *node,
                                     bf_jit_multiply_loop_plan *plan);
void bf_jit_build_multiply_term_plan(const bf_multiply_term *term,
                                     bf_jit_multiply_term_plan *plan);
int bf_jit_emit_multiply_terms_shared(const bf_ir_node *node,
                                      const bf_jit_multiply_term_ops *ops,
                                      void *context);
size_t bf_jit_block_size_hint_shared(const bf_ir_block *block,
                                     const bf_jit_size_hint_ops *ops);
int bf_jit_emit_block_with_pending_offset_shared(
    const bf_ir_block *block, int *pending_offset, int flush_pending_offset,
    const bf_jit_pending_offset_ops *ops, void *context);

int bf_runtime_execute(const bf_program *program, uint8_t *tape,
                       size_t tape_size);
int bf_runtime_execute_profiled(const bf_program *program, uint8_t *tape,
                                size_t tape_size, bf_runtime_profile *profile);
void bf_runtime_profile_dispose(bf_runtime_profile *profile);
int bf_runtime_read_byte(void);
void bf_runtime_write_byte(uint8_t value);
int bf_runtime_execute_scan(bf_jit_state *state, int step);
int bf_runtime_execute_multi_zero(bf_jit_state *state, const bf_ir_node *node);
int bf_runtime_execute_multiply_loop(bf_jit_state *state,
                                     const bf_ir_node *node);
size_t bf_runtime_scan_index(const uint8_t *tape, size_t tape_size,
                             size_t start_index, int64_t step);
size_t bf_runtime_scan_index_step4(const uint8_t *tape, size_t tape_size,
                                   size_t start_index);

#endif
