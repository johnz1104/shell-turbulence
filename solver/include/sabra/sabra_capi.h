/* C ABI for the fused Sabra RK4 core.
 *
 * Complex arrays are interleaved (re, im) doubles, which is the memory layout
 * of NumPy complex128. Callers own every buffer. Functions return a status
 * code and, on failure, write a NUL-terminated message into `error`.
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
const char* sabra_build_info(void);

int sabra_rhs(const sabra_model_spec* model, const double* state, double* result,
              char* error, size_t error_size);

int sabra_run_sampled(const sabra_model_spec* model, const double* initial,
                      double dt, long long total_steps, long long burn_in_steps,
                      long long sample_stride, long long progress_every_steps,
                      sabra_progress_fn progress, void* progress_context,
                      double* energy, double* dissipation, double* power_input,
                      double* shell_energy, double* burn_in_state,
                      double* final_state, char* error, size_t error_size);

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
