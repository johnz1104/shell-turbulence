/* C ABI for the fused Sabra RK4 core.
 *
 * Complex arrays are interleaved (re, im) doubles, which is the memory layout
 * of NumPy complex128. Callers own every buffer and must supply the lengths
 * documented below; the ABI cannot check allocated lengths. Array dimensions
 * use row-major order, and an interleaved complex value occupies two doubles.
 *
 * Computation functions return a SABRA_* status. If error != NULL and
 * error_size > 0, they write a NUL-terminated message (truncated to fit), or
 * an empty string on success. Otherwise no error text is written. Internal
 * exceptions are translated to SABRA_INTERNAL_ERROR; none cross the C ABI.
 */

#ifndef SABRA_CAPI_H
#define SABRA_CAPI_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

#define SABRA_ABI_VERSION 1

#define SABRA_OK 0
#define SABRA_INVALID_ARGUMENT 1
#define SABRA_NONFINITE 2
#define SABRA_CANCELLED 3
#define SABRA_INTERNAL_ERROR 4

#define SABRA_KERNEL_AUTOMATIC 0
#define SABRA_KERNEL_GENERIC 1

typedef struct {
  int shells;
  const double* wavenumbers;   /* (shells,) */
  const double* viscous_rates; /* (shells,) */
  const double* forcing;       /* interleaved complex (shells,) */
  double b;
  double c;
  double shell_ratio;
  int kernel; /* SABRA_KERNEL_AUTOMATIC or SABRA_KERNEL_GENERIC */
} sabra_model_spec;

/* Returns nonzero to cancel the run. */
typedef int (*sabra_progress_fn)(long long completed_steps, void* context);

int sabra_abi_version(void);
/* Library-owned static string; do not free or modify it. */
const char* sabra_build_info(void);

/* Evaluate the full RHS. model, its arrays, state and result must be non-NULL.
 * state and result each hold 2*shells doubles. The model requires shells >= 3,
 * finite coefficients/arrays and shell_ratio > 1; state must be finite.
 * Invalid specifications return SABRA_INVALID_ARGUMENT; nonfinite input state
 * returns SABRA_NONFINITE. Finite inputs do not guarantee finite RHS output.
 */
int sabra_rhs(const sabra_model_spec* model, const double* state, double* result,
              char* error, size_t error_size);

/* Integrate one state, recording S = total_steps/sample_stride + 1 samples at
 * steps 0, sample_stride, ..., total_steps. Burn-in does not discard samples.
 * dt must be positive and finite; total_steps and sample_stride positive;
 * total_steps and burn_in_steps must be multiples of sample_stride, with
 * 0 <= burn_in_steps < total_steps. progress_every_steps must be non-negative.
 *
 * All model/state/output pointers are required. initial, burn_in_state and
 * final_state hold 2*shells doubles each. energy, dissipation and power_input
 * hold S doubles each; shell_energy holds S*shells doubles. The input state
 * must be finite, and the state is checked again at each sample.
 *
 * If progress != NULL and progress_every_steps > 0, the callback runs after
 * recording a noninitial sample that reaches the next progress threshold,
 * and at the final sample. Thresholds falling between samples are coalesced;
 * completed_steps is the actual sampled step. The callback receives the
 * unchanged progress_context, may return nonzero to cancel, and must not
 * throw exceptions. Zero progress_every_steps disables callbacks.
 *
 * Cancellation returns SABRA_CANCELLED after recording that sample (and the
 * burn-in state if due). Later samples and final_state are not written, even
 * when cancellation occurs at the final callback. SABRA_NONFINITE can leave
 * a partially written sample; treat its outputs as incomplete. final_state
 * is written only on success. Other errors may also leave partial outputs.
 */
int sabra_run_sampled(const sabra_model_spec* model, const double* initial,
                      double dt, long long total_steps, long long burn_in_steps,
                      long long sample_stride, long long progress_every_steps,
                      sabra_progress_fn progress, void* progress_context,
                      double* energy, double* dissipation, double* power_input,
                      double* shell_energy, double* burn_in_state,
                      double* final_state, char* error, size_t error_size);

/* Integrate members independent states initialized as base_state + each
 * perturbation. The model rules above apply. dt must be positive and finite;
 * members, total_steps and sample_stride positive; total_steps must be a
 * multiple of sample_stride. threads >= 0 (zero selects hardware concurrency),
 * and 0 <= record_shells <= shells. At most members workers are used.
 *
 * Let S = total_steps/sample_stride + 1, including the initial state. All
 * pointers are required except recorded when record_shells == 0 (it is then
 * ignored), and the optional error buffer. Buffer lengths in elements:
 *   base_state:    2*shells doubles
 *   perturbations: 2*members*shells doubles
 *   energy, dissipation, power_input: members*S doubles each
 *   shell_energy:  members*S*shells doubles
 *   recorded:      2*members*S*record_shells doubles (first record_shells)
 *   final_states:  2*members*shells doubles
 *   status:        members ints; failure_step: members long longs
 * Base and perturbation inputs must be finite or the call returns
 * SABRA_NONFINITE before integration.
 *
 * SABRA_OK means the ensemble was processed; inspect each member's status:
 * SABRA_OK with failure_step == -1 means completion; SABRA_NONFINITE records
 * the first sampled step with a nonfinite state (not necessarily its first
 * failing integration step). That sample and all later samples, recorded
 * states and the final state are filled with NaN; other members continue.
 * A non-OK call status may leave partial outputs/statuses; they must not be
 * treated as a completed ensemble. Results are independent of thread count
 * for the same build and inputs.
 */
int sabra_run_ensemble(const sabra_model_spec* model, const double* base_state,
                       const double* perturbations, long long members, double dt,
                       long long total_steps, long long sample_stride,
                       int record_shells, int threads, double* energy,
                       double* dissipation, double* power_input,
                       double* shell_energy, double* recorded,
                       double* final_states, int* status,
                       long long* failure_step, char* error, size_t error_size);

#ifdef __cplusplus
}
#endif

#endif /* SABRA_CAPI_H */
