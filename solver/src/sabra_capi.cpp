// C ABI wrapper: validates pointers, converts exceptions to status codes and
// never lets a C++ exception cross the boundary.

#include "sabra/sabra_capi.h"

#include <cstdio>
#include <cstring>
#include <new>

#include "sabra/sabra.hpp"

#ifndef SABRA_BUILD_FLAGS
#define SABRA_BUILD_FLAGS "unrecorded"
#endif

#define SABRA_STRINGIFY_DETAIL(x) #x
#define SABRA_STRINGIFY(x) SABRA_STRINGIFY_DETAIL(x)

namespace {

void write_error(char* error, size_t error_size, const char* message) {
  if (error != nullptr && error_size > 0) {
    std::snprintf(error, error_size, "%s", message);
  }
}

sabra::Model model_from(const sabra_model_spec* spec) {
  if (spec == nullptr) {
    throw sabra::InvalidArgument("model specification must not be null");
  }
  if (spec->kernel != SABRA_KERNEL_AUTOMATIC && spec->kernel != SABRA_KERNEL_GENERIC) {
    throw sabra::InvalidArgument("unknown kernel selection");
  }
  return sabra::make_model(
      spec->shells, spec->wavenumbers, spec->viscous_rates, spec->forcing,
      spec->b, spec->c, spec->shell_ratio,
      spec->kernel == SABRA_KERNEL_GENERIC ? sabra::Kernel::generic
                                           : sabra::Kernel::automatic);
}

void require(bool condition, const char* message) {
  if (!condition) {
    throw sabra::InvalidArgument(message);
  }
}

template <class F>
int guarded(char* error, size_t error_size, F&& body) {
  try {
    body();
    write_error(error, error_size, "");
    return SABRA_OK;
  } catch (const sabra::InvalidArgument& e) {
    write_error(error, error_size, e.what());
    return SABRA_INVALID_ARGUMENT;
  } catch (const sabra::NonFinite& e) {
    write_error(error, error_size, e.what());
    return SABRA_NONFINITE;
  } catch (const sabra::Cancelled& e) {
    write_error(error, error_size, e.what());
    return SABRA_CANCELLED;
  } catch (const std::bad_alloc&) {
    write_error(error, error_size, "out of memory in compiled Sabra backend");
    return SABRA_INTERNAL_ERROR;
  } catch (const std::exception& e) {
    write_error(error, error_size, e.what());
    return SABRA_INTERNAL_ERROR;
  } catch (...) {
    write_error(error, error_size, "unknown error in compiled Sabra backend");
    return SABRA_INTERNAL_ERROR;
  }
}

}  // namespace

extern "C" {

int sabra_abi_version(void) { return SABRA_ABI_VERSION; }

const char* sabra_build_info(void) {
  static const char info[] =
      "abi=" SABRA_STRINGIFY(SABRA_ABI_VERSION)
      "; compiler="
#if defined(__clang__)
      "clang " __clang_version__
#elif defined(__GNUC__)
      "gcc " __VERSION__
#else
      "unknown"
#endif
      "; cplusplus=" SABRA_STRINGIFY(__cplusplus)
      "; flags=" SABRA_BUILD_FLAGS
#if defined(__FAST_MATH__)
      "; fast_math=ON"
#endif
      ;
  return info;
}

int sabra_rhs(const sabra_model_spec* model, const double* state, double* result,
              char* error, size_t error_size) {
  return guarded(error, error_size, [&] {
    const sabra::Model m = model_from(model);
    require(state != nullptr && result != nullptr, "state and result must not be null");
    sabra::evaluate_rhs(m, state, result);
  });
}

int sabra_run_sampled(const sabra_model_spec* model, const double* initial,
                      double dt, long long total_steps, long long burn_in_steps,
                      long long sample_stride, long long progress_every_steps,
                      sabra_progress_fn progress, void* progress_context,
                      double* energy, double* dissipation, double* power_input,
                      double* shell_energy, double* burn_in_state,
                      double* final_state, char* error, size_t error_size) {
  return guarded(error, error_size, [&] {
    const sabra::Model m = model_from(model);
    require(initial != nullptr && energy != nullptr && dissipation != nullptr &&
                power_input != nullptr && shell_energy != nullptr &&
                burn_in_state != nullptr && final_state != nullptr,
            "sampled-run buffers must not be null");
    sabra::SampledOutput out;
    out.energy = energy;
    out.dissipation = dissipation;
    out.power_input = power_input;
    out.shell_energy = shell_energy;
    out.burn_in_state = burn_in_state;
    out.final_state = final_state;
    sabra::run_sampled(m, initial, dt, total_steps, burn_in_steps, sample_stride,
                       progress_every_steps, progress, progress_context, out);
  });
}

int sabra_run_ensemble(const sabra_model_spec* model, const double* base_state,
                       const double* perturbations, long long members, double dt,
                       long long total_steps, long long sample_stride,
                       int record_shells, int threads, double* energy,
                       double* dissipation, double* power_input,
                       double* shell_energy, double* recorded,
                       double* final_states, int* status,
                       long long* failure_step, char* error, size_t error_size) {
  return guarded(error, error_size, [&] {
    const sabra::Model m = model_from(model);
    require(base_state != nullptr && perturbations != nullptr && energy != nullptr &&
                dissipation != nullptr && power_input != nullptr &&
                shell_energy != nullptr && final_states != nullptr &&
                status != nullptr && failure_step != nullptr,
            "ensemble buffers must not be null");
    require(record_shells == 0 || recorded != nullptr,
            "recorded buffer is required when record_shells is positive");
    sabra::EnsembleOutput out;
    out.energy = energy;
    out.dissipation = dissipation;
    out.power_input = power_input;
    out.shell_energy = shell_energy;
    out.recorded = record_shells ? recorded : nullptr;
    out.final_states = final_states;
    out.status = status;
    out.failure_step = failure_step;
    sabra::run_ensemble(m, base_state, perturbations, members, dt, total_steps,
                        sample_stride, record_shells, threads, out);
  });
}

}  // extern "C"
