// Public C ABI checks, using manufactured solutions rather than core internals.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <vector>

#include "sabra/sabra_capi.h"

namespace {

int failures = 0;
constexpr int shells = 3;
constexpr double untouched = -1234.5;
using State = std::array<double, 2 * shells>;

void check(bool condition, const char* label) {
  std::printf("%s: %s\n", condition ? "ok" : "FAIL", label);
  if (!condition) ++failures;
}

bool near(double actual, double expected) {
  return std::isfinite(actual) && std::abs(actual - expected) < 1e-13;
}

template <class Range>
bool all_equal(const Range& values, double expected) {
  return std::all_of(values.begin(), values.end(),
                     [=](double value) { return value == expected; });
}

struct Model {
  std::array<double, shells> k{1.0, 2.0, 4.0}, rates{1.0, 1.0, 1.0};
  State forcing{};

  sabra_model_spec spec() const {
    return {shells, k.data(), rates.data(), forcing.data(), 0.5, -0.5, 2.0,
            SABRA_KERNEL_AUTOMATIC};
  }
};

// With only shell 0 occupied and no forcing, all quadratic terms vanish.
// The RK4 amplification for u' = -u is known independently of this library.
double damped_amplitude(long long steps, double dt = 0.01) {
  const double factor = 1.0 - dt + dt * dt / 2.0 - dt * dt * dt / 6.0 +
                        dt * dt * dt * dt / 24.0;
  return std::pow(factor, steps);
}

struct Progress {
  std::vector<long long> steps;
  long long cancel_at = -1;
};

int progress(long long completed, void* context) {
  auto& trace = *static_cast<Progress*>(context);
  trace.steps.push_back(completed);
  return trace.cancel_at >= 0 && completed >= trace.cancel_at;
}

struct SampledRun {
  static constexpr int samples = 4;
  Model model;
  State initial{1.0, 0.0, 0.0, 0.0, 0.0, 0.0}, burn{}, final{};
  std::array<double, samples> energy{}, dissipation{}, power{};
  std::array<double, samples * shells> shell_energy{};
  double dt = 0.01;
  long long steps = 6, burn_step = 2, stride = 2, progress_every = 3;
  char error[128]{};

  SampledRun() {
    energy.fill(untouched);
    dissipation.fill(untouched);
    power.fill(untouched);
    shell_energy.fill(untouched);
    burn.fill(untouched);
    final.fill(untouched);
  }

  int run(Progress* trace = nullptr, bool omit_energy = false) {
    const auto specification = model.spec();
    return sabra_run_sampled(
        &specification, initial.data(), dt, steps, burn_step, stride, progress_every,
        trace ? progress : nullptr, trace, omit_energy ? nullptr : energy.data(),
        dissipation.data(), power.data(), shell_energy.data(), burn.data(),
        final.data(), error, sizeof error);
  }
};

void test_rhs_and_errors() {
  Model model;
  auto spec = model.spec();
  State initial{1.0, 0.0, 0.0, 0.0, 0.0, 0.0}, result{};
  char error[128] = "previous error";
  check(sabra_abi_version() == SABRA_ABI_VERSION &&
            std::strstr(sabra_build_info(), "abi=1") != nullptr,
        "shared library reports the expected ABI");
  check(sabra_rhs(&spec, initial.data(), result.data(), error, sizeof error) == SABRA_OK &&
            result == State{-1.0, 0.0, 0.0, 0.0, 0.0, 0.0} && error[0] == '\0',
        "RHS matches pure damping and clears stale error text");

  check(sabra_rhs(nullptr, initial.data(), result.data(), error, sizeof error) ==
            SABRA_INVALID_ARGUMENT && error[0] != '\0', "null model rejected with error text");
  check(sabra_rhs(&spec, nullptr, result.data(), nullptr, 0) == SABRA_INVALID_ARGUMENT &&
            sabra_rhs(&spec, initial.data(), nullptr, nullptr, 0) == SABRA_INVALID_ARGUMENT,
        "null RHS buffers rejected without requiring an error buffer");
  spec.kernel = -1;
  check(sabra_rhs(&spec, initial.data(), result.data(), error, sizeof error) ==
            SABRA_INVALID_ARGUMENT, "invalid kernel maps to invalid-argument status");
  spec = model.spec();
  spec.wavenumbers = nullptr;
  check(sabra_rhs(&spec, initial.data(), result.data(), error, sizeof error) ==
            SABRA_INVALID_ARGUMENT, "null model array rejected");

  char short_error[5] = {'x', 'x', 'x', 'x', '!'};
  sabra_rhs(nullptr, initial.data(), result.data(), short_error, 4);
  check(short_error[0] != '\0' && short_error[3] == '\0' && short_error[4] == '!',
        "truncated error is terminated without overwriting its buffer");
  char single = '!';
  sabra_rhs(nullptr, initial.data(), result.data(), &single, 0);
  check(single == '!', "zero-sized error buffer is not written");
  sabra_rhs(nullptr, initial.data(), result.data(), &single, 1);
  check(single == '\0', "one-byte error buffer contains only a terminator");
  check(sabra_rhs(nullptr, initial.data(), result.data(), nullptr, 12) == SABRA_INVALID_ARGUMENT,
        "null error pointer is allowed even with nonzero size");

  spec = model.spec();
  initial[0] = std::numeric_limits<double>::quiet_NaN();
  result.fill(untouched);
  check(sabra_rhs(&spec, initial.data(), result.data(), error, sizeof error) == SABRA_NONFINITE &&
            all_equal(result, untouched), "nonfinite RHS input rejected before output");
}

void test_sampled_solution() {
  SampledRun run;
  Progress trace;
  check(run.run(&trace) == SABRA_OK, "sampled manufactured solution succeeds");
  bool matches = true;
  for (int sample = 0; sample < SampledRun::samples; ++sample) {
    const double amplitude = damped_amplitude(2 * sample);
    matches = matches && near(run.energy[sample], 0.5 * amplitude * amplitude) &&
              near(run.dissipation[sample], amplitude * amplitude) &&
              run.power[sample] == 0.0;
    for (int shell = 0; shell < shells; ++shell) {
      matches = matches && near(run.shell_energy[sample * shells + shell],
                                shell == 0 ? 0.5 * amplitude * amplitude : 0.0);
    }
  }
  for (int component = 0; component < 2 * shells; ++component) {
    matches = matches && near(run.burn[component], component == 0 ? damped_amplitude(2) : 0.0) &&
              near(run.final[component], component == 0 ? damped_amplitude(6) : 0.0);
  }
  check(matches, "initial, intermediate, burn-in and final samples match damping polynomial");
  check(trace.steps == std::vector<long long>{4, 6}, "progress thresholds align to samples");

  SampledRun initial_burn;
  initial_burn.burn_step = 0;
  initial_burn.progress_every = 99;
  Progress final_trace;
  check(initial_burn.run(&final_trace) == SABRA_OK && initial_burn.burn == initial_burn.initial &&
            final_trace.steps == std::vector<long long>{6},
        "burn-in zero stores initial state and final callback precedes a distant threshold");
  SampledRun disabled;
  disabled.progress_every = 0;
  Progress disabled_trace;
  check(disabled.run(&disabled_trace) == SABRA_OK && disabled_trace.steps.empty(),
        "zero progress interval disables callbacks");
}

void test_sampled_cancellation() {
  for (long long cancel_at : {4, 6}) {
    SampledRun run;
    Progress trace;
    trace.cancel_at = cancel_at;
    const int status = run.run(&trace);
    const int last_sample = static_cast<int>(cancel_at / run.stride);
    bool boundary = true;
    for (int sample = 0; sample < SampledRun::samples; ++sample) {
      boundary = boundary && (sample <= last_sample ? std::isfinite(run.energy[sample]) &&
                                  run.energy[sample] >= 0.0 : run.energy[sample] == untouched);
    }
    check(status == SABRA_CANCELLED && run.error[0] != '\0' && boundary &&
              near(run.burn[0], damped_amplitude(2)) && all_equal(run.final, untouched) &&
              !trace.steps.empty() && trace.steps.back() == cancel_at,
          "cancellation preserves completed samples and leaves final state unwritten");
  }
}

void test_sampled_rejections() {
  struct Schedule { long long steps, burn, stride, progress; };
  for (const Schedule invalid : {Schedule{0, 0, 2, 3}, {6, 2, 0, 3}, {5, 2, 2, 3},
                                 {6, -1, 2, 3}, {6, 6, 2, 3}, {6, 1, 2, 3}, {6, 2, 2, -1}}) {
    SampledRun run;
    run.steps = invalid.steps;
    run.burn_step = invalid.burn;
    run.stride = invalid.stride;
    run.progress_every = invalid.progress;
    check(run.run() == SABRA_INVALID_ARGUMENT && all_equal(run.energy, untouched),
          "invalid sample schedule rejected before output");
  }
  for (double dt : {0.0, -1.0, std::numeric_limits<double>::infinity()}) {
    SampledRun run;
    run.dt = dt;
    check(run.run() == SABRA_INVALID_ARGUMENT, "invalid sampled timestep rejected");
  }
  SampledRun missing;
  check(missing.run(nullptr, true) == SABRA_INVALID_ARGUMENT, "required sampled buffer rejected");
  SampledRun nonfinite;
  nonfinite.initial[0] = std::numeric_limits<double>::infinity();
  check(nonfinite.run() == SABRA_NONFINITE && all_equal(nonfinite.energy, untouched),
        "nonfinite initial sampled state maps to nonfinite status");
  SampledRun overflow;
  overflow.initial[2] = overflow.initial[4] = 1e200;
  check(overflow.run() == SABRA_NONFINITE && all_equal(overflow.final, untouched),
        "nonfinite integration maps to nonfinite status without a final state");
}

struct EnsembleRun {
  static constexpr int members = 2, samples = 3, steps = 2;
  Model model;
  State base{1.0, 0.0, 0.0, 0.0, 0.0, 0.0};
  std::array<double, 2 * members * shells> perturbations{}, final{};
  std::array<double, members * samples> energy{}, dissipation{}, power{};
  std::array<double, members * samples * shells> shell_energy{};
  std::array<double, 2 * members * samples> recorded{};  // one complex shell
  std::array<int, members> status{-1, -1};
  std::array<long long, members> failure{-2, -2};
  char error[128]{};

  int run(int record_shells = 1, bool omit_recorded = false) {
    const auto specification = model.spec();
    return sabra_run_ensemble(
        &specification, base.data(), perturbations.data(), members, 0.01, steps, 1,
        record_shells, 2, energy.data(), dissipation.data(), power.data(), shell_energy.data(),
        omit_recorded ? nullptr : recorded.data(), final.data(), status.data(), failure.data(),
        error, sizeof error);
  }
};

void test_ensemble_statuses() {
  EnsembleRun run;
  // A finite initial state overflows in its first RK4 step for member 1 only.
  run.perturbations[2 * shells + 2] = run.perturbations[2 * shells + 4] = 1e200;
  check(run.run() == SABRA_OK && run.error[0] == '\0',
        "ensemble call succeeds even when one member becomes nonfinite");
  check(run.status[0] == SABRA_OK && run.failure[0] == -1 &&
            run.status[1] == SABRA_NONFINITE && run.failure[1] == 1,
        "member statuses distinguish completion from first nonfinite sample");
  bool successful = near(run.final[0], damped_amplitude(2));
  bool failed = true;
  for (int sample = 0; sample < EnsembleRun::samples; ++sample) {
    const double amplitude = damped_amplitude(sample);
    successful = successful && near(run.energy[sample], 0.5 * amplitude * amplitude) &&
                 near(run.recorded[2 * sample], amplitude) && run.recorded[2 * sample + 1] == 0.0;
    if (sample == 0) continue;
    const int index = EnsembleRun::samples + sample;
    failed = failed && std::isnan(run.energy[index]) && std::isnan(run.dissipation[index]) &&
             std::isnan(run.power[index]);
    for (int shell = 0; shell < shells; ++shell) {
      failed = failed && std::isnan(run.shell_energy[index * shells + shell]);
    }
    failed = failed && std::isnan(run.recorded[2 * index]) && std::isnan(run.recorded[2 * index + 1]);
  }
  for (int component = 0; component < 2 * shells; ++component) {
    failed = failed && std::isnan(run.final[2 * shells + component]);
  }
  check(successful && failed, "member buffer slices preserve successful output and fill failed tails");

  EnsembleRun no_recording;
  check(no_recording.run(0, true) == SABRA_OK && no_recording.status[0] == SABRA_OK &&
            no_recording.status[1] == SABRA_OK, "recorded buffer is optional with zero recorded shells");
  EnsembleRun missing;
  check(missing.run(1, true) == SABRA_INVALID_ARGUMENT, "recorded buffer required for positive count");
  EnsembleRun nonfinite;
  nonfinite.perturbations[0] = std::numeric_limits<double>::quiet_NaN();
  check(nonfinite.run() == SABRA_NONFINITE && nonfinite.status == std::array<int, 2>{-1, -1},
        "nonfinite ensemble input rejects whole call before member processing");
}

}  // namespace

int main() {
  test_rhs_and_errors();
  test_sampled_solution();
  test_sampled_cancellation();
  test_sampled_rejections();
  test_ensemble_statuses();
  if (failures) std::printf("%d C ABI check(s) failed\n", failures);
  return failures ? EXIT_FAILURE : EXIT_SUCCESS;
}
