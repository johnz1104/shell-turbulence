// Fused fixed-step RK4 core for the Li et al. (2025) Sabra convention.
//
// Every expression uses plain IEEE-754 operations in a fixed order. Compile
// with -ffp-contract=off and without -ffast-math, as CMakeLists.txt does, so
// the compiler adds no fused multiply-add or reassociation; results are then
// repeatable and independent of kernel dispatch and thread count.
//
// Shells are numbered n=1..N in the physics; storage index j=n-1. Integrated
// states are held as separate real and imaginary arrays with two explicit
// zero ghost shells on each side, which makes the shell loop branch-free.

#pragma once

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <stdexcept>
#include <string>
#include <thread>
#include <type_traits>
#include <utility>
#include <vector>

namespace sabra {

constexpr int kGhost = 2;
constexpr int kMinShells = 3;
constexpr int kMaxFixedShells = 40;

class InvalidArgument : public std::invalid_argument {
 public:
  using std::invalid_argument::invalid_argument;
};

class NonFinite : public std::runtime_error {
 public:
  using std::runtime_error::runtime_error;
};

class Cancelled : public std::runtime_error {
 public:
  using std::runtime_error::runtime_error;
};

// Returns nonzero to request cancellation.
using ProgressFn = int (*)(long long completed_steps, void* context);

enum class Kernel { automatic, generic };

struct Model {
  int shells = 0;
  double b = 0.0;
  double c = 0.0;
  double shell_ratio = 0.0;
  Kernel kernel = Kernel::automatic;
  std::vector<double> viscous_rates;
  std::vector<double> forcing_re;
  std::vector<double> forcing_im;
  std::vector<double> coef_a;  // k_n
  std::vector<double> coef_b;  // b * (k_n / q)
  std::vector<double> coef_c;  // c * (k_n / (q * q))
};

inline bool finite(double value) { return std::isfinite(value); }

// wavenumbers and viscous_rates have length shells; forcing is interleaved
// complex (re, im) of length 2*shells, matching NumPy complex128 storage.
inline Model make_model(int shells, const double* wavenumbers,
                        const double* viscous_rates, const double* forcing,
                        double b, double c, double shell_ratio,
                        Kernel kernel = Kernel::automatic) {
  if (shells < kMinShells) {
    throw InvalidArgument("at least three shells are required");
  }
  if (wavenumbers == nullptr || viscous_rates == nullptr || forcing == nullptr) {
    throw InvalidArgument("model arrays must not be null");
  }
  if (!(shell_ratio > 1.0) || !finite(shell_ratio)) {
    throw InvalidArgument("shell_ratio must be finite and greater than one");
  }
  if (!finite(b) || !finite(c)) {
    throw InvalidArgument("b and c must be finite");
  }
  Model model;
  model.shells = shells;
  model.b = b;
  model.c = c;
  model.shell_ratio = shell_ratio;
  model.kernel = kernel;
  model.viscous_rates.assign(viscous_rates, viscous_rates + shells);
  model.forcing_re.resize(shells);
  model.forcing_im.resize(shells);
  model.coef_a.resize(shells);
  model.coef_b.resize(shells);
  model.coef_c.resize(shells);
  const double q = shell_ratio;
  const double q2 = q * q;
  for (int j = 0; j < shells; ++j) {
    const double k = wavenumbers[j];
    if (!finite(k) || !finite(viscous_rates[j]) || !finite(forcing[2 * j]) ||
        !finite(forcing[2 * j + 1])) {
      throw InvalidArgument("model arrays must contain only finite values");
    }
    model.forcing_re[j] = forcing[2 * j];
    model.forcing_im[j] = forcing[2 * j + 1];
    model.coef_a[j] = k;
    model.coef_b[j] = b * (k / q);
    model.coef_c[j] = c * (k / q2);
  }
  return model;
}

// Ghost-padded state plus the four RK4 slopes.
struct Workspace {
  explicit Workspace(int shells)
      : ur(shells + 2 * kGhost, 0.0),
        ui(shells + 2 * kGhost, 0.0),
        tr(shells + 2 * kGhost, 0.0),
        ti(shells + 2 * kGhost, 0.0),
        k1r(shells), k1i(shells), k2r(shells), k2i(shells),
        k3r(shells), k3i(shells), k4r(shells), k4i(shells) {}

  void load(const double* interleaved, int shells) {
    for (int j = 0; j < shells; ++j) {
      ur[j + kGhost] = interleaved[2 * j];
      ui[j + kGhost] = interleaved[2 * j + 1];
    }
  }

  void store(double* interleaved, int shells) const {
    for (int j = 0; j < shells; ++j) {
      interleaved[2 * j] = ur[j + kGhost];
      interleaved[2 * j + 1] = ui[j + kGhost];
    }
  }

  std::vector<double> ur, ui, tr, ti;
  std::vector<double> k1r, k1i, k2r, k2i, k3r, k3i, k4r, k4i;
};

// Full RHS on ghost-padded input (index j+kGhost is shell j+1):
//   i*(k u_{n+2} conj(u_{n+1}) - b(k/q) u_{n+1} conj(u_{n-1})
//      - c(k/q^2) u_{n-1} u_{n-2}) - nu k^2 u_n + f_n.
// Count is int or std::integral_constant<int, N>; the latter fully unrolls.
template <class Count>
inline void rhs(const Model& model, Count count, const double* __restrict ur,
                const double* __restrict ui, double* __restrict rr,
                double* __restrict ri) {
  const int n = static_cast<int>(count);
  const double* __restrict ca = model.coef_a.data();
  const double* __restrict cb = model.coef_b.data();
  const double* __restrict cc = model.coef_c.data();
  const double* __restrict nu = model.viscous_rates.data();
  const double* __restrict fr = model.forcing_re.data();
  const double* __restrict fi = model.forcing_im.data();
  for (int j = 0; j < n; ++j) {
    const int p = j + kGhost;
    // (k * u_{n+2}) * conj(u_{n+1})
    const double xr = ca[j] * ur[p + 2];
    const double xi = ca[j] * ui[p + 2];
    const double ar = xr * ur[p + 1] + xi * ui[p + 1];
    const double ai = xi * ur[p + 1] - xr * ui[p + 1];
    // (b (k/q) * u_{n+1}) * conj(u_{n-1})
    const double yr = cb[j] * ur[p + 1];
    const double yi = cb[j] * ui[p + 1];
    const double br = yr * ur[p - 1] + yi * ui[p - 1];
    const double bi = yi * ur[p - 1] - yr * ui[p - 1];
    // (c (k/q^2) * u_{n-1}) * u_{n-2}
    const double zr = cc[j] * ur[p - 1];
    const double zi = cc[j] * ui[p - 1];
    const double cr = zr * ur[p - 2] - zi * ui[p - 2];
    const double ci = zr * ui[p - 2] + zi * ur[p - 2];
    const double sr = (ar - br) - cr;
    const double si = (ai - bi) - ci;
    // 1j * s - nu k^2 u + f
    rr[j] = (-si - nu[j] * ur[p]) + fr[j];
    ri[j] = (sr - nu[j] * ui[p]) + fi[j];
  }
}

// One classical RK4 step of the state held in workspace.ur/ui.
template <class Count>
inline void rk4_step(const Model& model, Count count, double dt, double half_dt,
                     double sixth_dt, Workspace& w) {
  const int n = static_cast<int>(count);
  double* __restrict ur = w.ur.data();
  double* __restrict ui = w.ui.data();
  double* __restrict tr = w.tr.data();
  double* __restrict ti = w.ti.data();
  double* __restrict k1r = w.k1r.data();
  double* __restrict k1i = w.k1i.data();
  double* __restrict k2r = w.k2r.data();
  double* __restrict k2i = w.k2i.data();
  double* __restrict k3r = w.k3r.data();
  double* __restrict k3i = w.k3i.data();
  double* __restrict k4r = w.k4r.data();
  double* __restrict k4i = w.k4i.data();

  rhs(model, count, ur, ui, k1r, k1i);
  for (int j = 0; j < n; ++j) {
    tr[j + kGhost] = ur[j + kGhost] + half_dt * k1r[j];
    ti[j + kGhost] = ui[j + kGhost] + half_dt * k1i[j];
  }
  rhs(model, count, tr, ti, k2r, k2i);
  for (int j = 0; j < n; ++j) {
    tr[j + kGhost] = ur[j + kGhost] + half_dt * k2r[j];
    ti[j + kGhost] = ui[j + kGhost] + half_dt * k2i[j];
  }
  rhs(model, count, tr, ti, k3r, k3i);
  for (int j = 0; j < n; ++j) {
    tr[j + kGhost] = ur[j + kGhost] + dt * k3r[j];
    ti[j + kGhost] = ui[j + kGhost] + dt * k3i[j];
  }
  rhs(model, count, tr, ti, k4r, k4i);
  for (int j = 0; j < n; ++j) {
    ur[j + kGhost] =
        ur[j + kGhost] +
        sixth_dt * (((k1r[j] + 2.0 * k2r[j]) + 2.0 * k3r[j]) + k4r[j]);
    ui[j + kGhost] =
        ui[j + kGhost] +
        sixth_dt * (((k1i[j] + 2.0 * k2i[j]) + 2.0 * k3i[j]) + k4i[j]);
  }
}

struct StepSizes {
  explicit StepSizes(double step) : dt(step), half(0.5 * step), sixth(step / 6.0) {}
  double dt, half, sixth;
};

template <class Count>
inline void advance(const Model& model, Count count, const StepSizes& h,
                    long long steps, Workspace& w) {
  for (long long s = 0; s < steps; ++s) {
    rk4_step(model, count, h.dt, h.half, h.sixth, w);
  }
}

// Sampled diagnostics: energy, dissipation, power input and per-shell energy.
// Returns false if any state component is not finite.
template <class Count>
inline bool record(const Model& model, Count count, const Workspace& w,
                   double* shell_energy, double& energy, double& dissipation,
                   double& power) {
  const int n = static_cast<int>(count);
  double energy_total = 0.0;
  double dissipation_total = 0.0;
  double power_total = 0.0;
  for (int j = 0; j < n; ++j) {
    const double re = w.ur[j + kGhost];
    const double im = w.ui[j + kGhost];
    if (!finite(re) || !finite(im)) {
      return false;
    }
    const double magnitude_squared = re * re + im * im;
    if (shell_energy != nullptr) {
      shell_energy[j] = 0.5 * magnitude_squared;
    }
    energy_total = energy_total + 0.5 * magnitude_squared;
    dissipation_total = dissipation_total + model.viscous_rates[j] * magnitude_squared;
    power_total = power_total + (re * model.forcing_re[j] + im * model.forcing_im[j]);
  }
  energy = energy_total;
  dissipation = dissipation_total;
  power = power_total;
  return true;
}

// Calls f(count) with a compile-time shell count when one is instantiated.
template <class F>
inline void dispatch(const Model& model, F&& f) {
  if (model.kernel == Kernel::generic) {
    f(model.shells);
    return;
  }
  switch (model.shells) {
#define SABRA_FIXED_CASE(N)                   \
  case N:                                     \
    f(std::integral_constant<int, N>{});      \
    return;
    SABRA_FIXED_CASE(3) SABRA_FIXED_CASE(4) SABRA_FIXED_CASE(5)
    SABRA_FIXED_CASE(6) SABRA_FIXED_CASE(7) SABRA_FIXED_CASE(8)
    SABRA_FIXED_CASE(9) SABRA_FIXED_CASE(10) SABRA_FIXED_CASE(11)
    SABRA_FIXED_CASE(12) SABRA_FIXED_CASE(13) SABRA_FIXED_CASE(14)
    SABRA_FIXED_CASE(15) SABRA_FIXED_CASE(16) SABRA_FIXED_CASE(17)
    SABRA_FIXED_CASE(18) SABRA_FIXED_CASE(19) SABRA_FIXED_CASE(20)
    SABRA_FIXED_CASE(21) SABRA_FIXED_CASE(22) SABRA_FIXED_CASE(23)
    SABRA_FIXED_CASE(24) SABRA_FIXED_CASE(25) SABRA_FIXED_CASE(26)
    SABRA_FIXED_CASE(27) SABRA_FIXED_CASE(28) SABRA_FIXED_CASE(29)
    SABRA_FIXED_CASE(30) SABRA_FIXED_CASE(31) SABRA_FIXED_CASE(32)
    SABRA_FIXED_CASE(33) SABRA_FIXED_CASE(34) SABRA_FIXED_CASE(35)
    SABRA_FIXED_CASE(36) SABRA_FIXED_CASE(37) SABRA_FIXED_CASE(38)
    SABRA_FIXED_CASE(39) SABRA_FIXED_CASE(40)
#undef SABRA_FIXED_CASE
    default:
      f(model.shells);
      return;
  }
}

inline void validate_step(double dt) {
  if (!(dt > 0.0) || !finite(dt)) {
    throw InvalidArgument("dt must be positive and finite");
  }
}

inline void validate_state(const double* interleaved, int shells) {
  for (int j = 0; j < 2 * shells; ++j) {
    if (!finite(interleaved[j])) {
      throw NonFinite("compiled Sabra state contains NaN or infinity");
    }
  }
}

// Single RHS evaluation; state and result are interleaved complex.
inline void evaluate_rhs(const Model& model, const double* state, double* result) {
  validate_state(state, model.shells);
  Workspace w(model.shells);
  w.load(state, model.shells);
  dispatch(model, [&](auto count) {
    rhs(model, count, w.ur.data(), w.ui.data(), w.k1r.data(), w.k1i.data());
  });
  for (int j = 0; j < model.shells; ++j) {
    result[2 * j] = w.k1r[j];
    result[2 * j + 1] = w.k1i[j];
  }
}

struct SampledOutput {
  double* energy = nullptr;        // (samples,)
  double* dissipation = nullptr;   // (samples,)
  double* power_input = nullptr;   // (samples,)
  double* shell_energy = nullptr;  // (samples, shells)
  double* burn_in_state = nullptr; // interleaved (shells,)
  double* final_state = nullptr;   // interleaved (shells,)
};

// Fixed-stride diagnostics including the initial state, a finite check at
// every sample, the state at burn_in_steps and the final state.
inline void run_sampled(const Model& model, const double* initial, double dt,
                        long long total_steps, long long burn_in_steps,
                        long long sample_stride, long long progress_every_steps,
                        ProgressFn progress, void* progress_context,
                        const SampledOutput& out) {
  validate_step(dt);
  if (total_steps <= 0 || sample_stride <= 0) {
    throw InvalidArgument("total_steps and sample_stride must be positive");
  }
  if (burn_in_steps < 0 || burn_in_steps >= total_steps) {
    throw InvalidArgument("burn_in_steps must lie in [0,total_steps)");
  }
  if (total_steps % sample_stride || burn_in_steps % sample_stride) {
    throw InvalidArgument("total_steps and burn_in_steps must align with samples");
  }
  if (progress_every_steps < 0) {
    throw InvalidArgument("progress_every_steps must be non-negative");
  }
  validate_state(initial, model.shells);

  const int shells = model.shells;
  const long long sample_count = total_steps / sample_stride + 1;
  const StepSizes h(dt);
  Workspace w(shells);
  w.load(initial, shells);

  dispatch(model, [&](auto count) {
    long long next_progress = progress_every_steps;
    for (long long sample = 0; sample < sample_count; ++sample) {
      double* shell_row =
          out.shell_energy ? out.shell_energy + sample * shells : nullptr;
      if (!record(model, count, w, shell_row, out.energy[sample],
                  out.dissipation[sample], out.power_input[sample])) {
        throw NonFinite("compiled Sabra state contains NaN or infinity");
      }
      const long long completed = sample * sample_stride;
      if (completed == burn_in_steps) {
        w.store(out.burn_in_state, shells);
      }
      if (sample > 0 && progress != nullptr && progress_every_steps) {
        if (completed >= next_progress || completed == total_steps) {
          if (progress(completed, progress_context)) {
            throw Cancelled("compiled Sabra run cancelled by progress callback");
          }
          while (next_progress <= completed) {
            next_progress += progress_every_steps;
          }
        }
      }
      if (sample + 1 == sample_count) {
        break;
      }
      advance(model, count, h, sample_stride, w);
    }
  });
  w.store(out.final_state, shells);
}

enum MemberStatus : int { member_completed = 0, member_nonfinite = 2 };

struct EnsembleOutput {
  double* energy = nullptr;        // (members, samples)
  double* dissipation = nullptr;   // (members, samples)
  double* power_input = nullptr;   // (members, samples)
  double* shell_energy = nullptr;  // (members, samples, shells)
  double* recorded = nullptr;      // interleaved (members, samples, record_shells)
  double* final_states = nullptr;  // interleaved (members, shells)
  int* status = nullptr;           // (members,)
  long long* failure_step = nullptr;  // (members,), -1 when completed
};

// Advance every member from base + perturbation[m]. Each member is integrated
// serially by exactly one thread, so results do not depend on thread count.
// A member whose state becomes non-finite is marked and its remaining samples
// and final state are NaN; other members continue.
inline void run_ensemble(const Model& model, const double* base,
                         const double* perturbations, long long members,
                         double dt, long long total_steps,
                         long long sample_stride, int record_shells,
                         int threads, const EnsembleOutput& out) {
  validate_step(dt);
  if (members <= 0) {
    throw InvalidArgument("members must be positive");
  }
  if (total_steps <= 0 || sample_stride <= 0) {
    throw InvalidArgument("total_steps and sample_stride must be positive");
  }
  if (total_steps % sample_stride) {
    throw InvalidArgument("total_steps must align with samples");
  }
  if (record_shells < 0 || record_shells > model.shells) {
    throw InvalidArgument("record_shells must lie in [0,n_shells]");
  }
  if (threads < 0) {
    throw InvalidArgument("threads must be non-negative");
  }
  const int shells = model.shells;
  validate_state(base, shells);
  for (long long m = 0; m < members; ++m) {
    validate_state(perturbations + 2 * shells * m, shells);
  }

  const long long sample_count = total_steps / sample_stride + 1;
  const StepSizes h(dt);
  const double nan = std::nan("");

  auto run_member = [&](long long m, Workspace& w) {
    const double* eta = perturbations + 2 * shells * m;
    for (int j = 0; j < shells; ++j) {
      w.ur[j + kGhost] = base[2 * j] + eta[2 * j];
      w.ui[j + kGhost] = base[2 * j + 1] + eta[2 * j + 1];
    }
    double* energy = out.energy + m * sample_count;
    double* dissipation = out.dissipation + m * sample_count;
    double* power = out.power_input + m * sample_count;
    double* shell_energy = out.shell_energy + m * sample_count * shells;
    double* recorded = out.recorded ? out.recorded + 2 * m * sample_count * record_shells
                                    : nullptr;
    double* final_state = out.final_states + 2 * m * shells;
    out.status[m] = member_completed;
    out.failure_step[m] = -1;
    dispatch(model, [&](auto count) {
      for (long long sample = 0; sample < sample_count; ++sample) {
        if (!record(model, count, w, shell_energy + sample * shells,
                    energy[sample], dissipation[sample], power[sample])) {
          out.status[m] = member_nonfinite;
          out.failure_step[m] = sample * sample_stride;
          for (long long rest = sample; rest < sample_count; ++rest) {
            energy[rest] = nan;
            dissipation[rest] = nan;
            power[rest] = nan;
            std::fill(shell_energy + rest * shells,
                      shell_energy + (rest + 1) * shells, nan);
            if (recorded) {
              std::fill(recorded + 2 * rest * record_shells,
                        recorded + 2 * (rest + 1) * record_shells, nan);
            }
          }
          std::fill(final_state, final_state + 2 * shells, nan);
          return;
        }
        if (recorded) {
          double* row = recorded + 2 * sample * record_shells;
          for (int j = 0; j < record_shells; ++j) {
            row[2 * j] = w.ur[j + kGhost];
            row[2 * j + 1] = w.ui[j + kGhost];
          }
        }
        if (sample + 1 == sample_count) {
          break;
        }
        advance(model, count, h, sample_stride, w);
      }
      w.store(final_state, shells);
    });
  };

  long long workers = threads > 0 ? threads
                                  : std::max(1u, std::thread::hardware_concurrency());
  workers = std::min(workers, members);
  std::atomic<long long> next_member{0};
  std::exception_ptr failure;
  std::atomic<bool> failed{false};
  auto work = [&]() {
    try {
      Workspace w(shells);
      for (;;) {
        if (failed.load()) {
          return;
        }
        const long long m = next_member.fetch_add(1);
        if (m >= members) {
          return;
        }
        run_member(m, w);
      }
    } catch (...) {
      bool expected = false;
      if (failed.compare_exchange_strong(expected, true)) {
        failure = std::current_exception();
      }
    }
  };
  std::vector<std::thread> pool;
  pool.reserve(static_cast<std::size_t>(workers - 1));
  for (long long t = 1; t < workers; ++t) {
    pool.emplace_back(work);
  }
  work();
  for (auto& thread : pool) {
    thread.join();
  }
  if (failure) {
    std::rethrow_exception(failure);
  }
}

}  // namespace sabra
