// Native checks for the fused Sabra core.

#include <cmath>
#include <complex>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <vector>

#include "sabra/sabra.hpp"

namespace {

int failures = 0;

void check(bool condition, const char* what) {
  if (!condition) {
    std::printf("FAIL: %s\n", what);
    ++failures;
  } else {
    std::printf("ok:   %s\n", what);
  }
}

struct Setup {
  int shells;
  std::vector<double> k, nu, f;
  double b = 0.5, c = -0.5, q = 2.0;
};

Setup make_setup(int shells, double viscosity, double force_re, double force_im) {
  Setup s;
  s.shells = shells;
  s.k.resize(shells);
  s.nu.resize(shells);
  s.f.assign(2 * shells, 0.0);
  for (int j = 0; j < shells; ++j) {
    s.k[j] = 0.05 * std::pow(2.0, j + 1);
    s.nu[j] = viscosity * s.k[j] * s.k[j];
  }
  s.f[0] = force_re;
  s.f[1] = force_im;
  return s;
}

sabra::Model model_of(const Setup& s, sabra::Kernel kernel = sabra::Kernel::automatic) {
  return sabra::make_model(s.shells, s.k.data(), s.nu.data(), s.f.data(), s.b, s.c,
                           s.q, kernel);
}

std::vector<double> random_state(int shells, unsigned seed, double scale = 1.0) {
  std::mt19937_64 rng(seed);
  std::normal_distribution<double> normal(0.0, scale);
  std::vector<double> state(2 * shells);
  for (double& value : state) {
    value = normal(rng);
  }
  return state;
}

// Independent branchy formulation with std::complex.
std::vector<std::complex<double>> reference_rhs(const Setup& s,
                                                const std::vector<double>& state) {
  using C = std::complex<double>;
  const int n = s.shells;
  std::vector<C> u(n), out(n);
  for (int j = 0; j < n; ++j) {
    u[j] = C(state[2 * j], state[2 * j + 1]);
  }
  for (int j = 0; j < n; ++j) {
    C term = 0.0;
    if (j + 2 < n) term += s.k[j] * u[j + 2] * std::conj(u[j + 1]);
    if (j >= 1 && j + 1 < n) term -= s.b * s.k[j] / s.q * u[j + 1] * std::conj(u[j - 1]);
    if (j >= 2) term -= s.c * s.k[j] / (s.q * s.q) * u[j - 1] * u[j - 2];
    out[j] = C(0.0, 1.0) * term - s.nu[j] * u[j] + C(s.f[2 * j], s.f[2 * j + 1]);
  }
  return out;
}

void test_rhs_against_reference() {
  for (int shells : {3, 4, 5, 9, 14, 22, 41}) {
    const Setup s = make_setup(shells, 3.7e-4, 0.004, -0.006);
    const sabra::Model model = model_of(s);
    const std::vector<double> state = random_state(shells, 832u + shells);
    std::vector<double> result(2 * shells);
    sabra::evaluate_rhs(model, state.data(), result.data());
    const auto expected = reference_rhs(s, state);
    double worst = 0.0;
    for (int j = 0; j < shells; ++j) {
      const double scale = 1e-300 + std::abs(expected[j]);
      worst = std::max(worst, std::abs(std::complex<double>(result[2 * j], result[2 * j + 1]) -
                                       expected[j]) / std::max(scale, 1.0));
    }
    char label[96];
    std::snprintf(label, sizeof label, "RHS matches branchy reference at N=%d (%.2e)", shells, worst);
    check(worst < 1e-14, label);
  }
}

void test_nonlinear_energy_cancellation() {
  for (int shells : {3, 7, 14, 22}) {
    Setup s = make_setup(shells, 0.0, 0.0, 0.0);
    const sabra::Model model = model_of(s);
    const std::vector<double> state = random_state(shells, 17u + shells);
    std::vector<double> result(2 * shells);
    sabra::evaluate_rhs(model, state.data(), result.data());
    double rate = 0.0, scale = 0.0;
    for (int j = 0; j < 2 * shells; ++j) {
      rate += state[j] * result[j];
      scale += std::abs(state[j] * result[j]);
    }
    char label[96];
    std::snprintf(label, sizeof label, "Re<u,N(u)> = 0 to round-off at N=%d (%.2e)", shells,
                  std::abs(rate) / scale);
    check(std::abs(rate) <= 1e-14 * scale, label);
  }
}

std::vector<double> integrate(const sabra::Model& model, const std::vector<double>& initial,
                              double dt, long long steps) {
  sabra::Workspace w(model.shells);
  w.load(initial.data(), model.shells);
  const sabra::StepSizes h(dt);
  sabra::dispatch(model, [&](auto count) { sabra::advance(model, count, h, steps, w); });
  std::vector<double> out(2 * model.shells);
  w.store(out.data(), model.shells);
  return out;
}

double distance(const std::vector<double>& a, const std::vector<double>& b) {
  double total = 0.0;
  for (std::size_t i = 0; i < a.size(); ++i) total += (a[i] - b[i]) * (a[i] - b[i]);
  return std::sqrt(total);
}

void test_rk4_fourth_order() {
  const Setup s = make_setup(6, 1.0e-3, 0.05, 0.02);
  const sabra::Model model = model_of(s);
  const std::vector<double> initial = random_state(6, 4u, 0.3);
  const double horizon = 0.8;
  const auto reference = integrate(model, initial, horizon / 3200, 3200);
  const double e1 = distance(integrate(model, initial, horizon / 50, 50), reference);
  const double e2 = distance(integrate(model, initial, horizon / 100, 100), reference);
  const double ratio = e1 / e2;
  char label[96];
  std::snprintf(label, sizeof label, "RK4 halving ratio near 16 (%.3f)", ratio);
  check(ratio > 14.0 && ratio < 18.0, label);
}

void test_fixed_and_generic_kernels_bitwise() {
  for (int shells : {3, 14, 22, 40, 45}) {
    const Setup s = make_setup(shells, 1.0e-4, 0.005, 0.005);
    const std::vector<double> initial = random_state(shells, 99u, 0.2);
    const auto fixed = integrate(model_of(s), initial, 1.0e-5, 3000);
    const auto generic = integrate(model_of(s, sabra::Kernel::generic), initial, 1.0e-5, 3000);
    char label[96];
    std::snprintf(label, sizeof label, "fixed-N and generic kernels bitwise equal at N=%d", shells);
    check(std::memcmp(fixed.data(), generic.data(), fixed.size() * sizeof(double)) == 0, label);
  }
}

struct EnsembleBuffers {
  EnsembleBuffers(long long members, long long samples, int shells, int record)
      : energy(members * samples), dissipation(members * samples), power(members * samples),
        shell_energy(members * samples * shells), recorded(2 * members * samples * record),
        final_states(2 * members * shells), status(members), failure(members) {}
  sabra::EnsembleOutput view() {
    sabra::EnsembleOutput out;
    out.energy = energy.data();
    out.dissipation = dissipation.data();
    out.power_input = power.data();
    out.shell_energy = shell_energy.data();
    out.recorded = recorded.empty() ? nullptr : recorded.data();
    out.final_states = final_states.data();
    out.status = status.data();
    out.failure_step = failure.data();
    return out;
  }
  bool same(const EnsembleBuffers& o) const {
    auto eq = [](const std::vector<double>& a, const std::vector<double>& b) {
      return a.size() == b.size() && std::memcmp(a.data(), b.data(), a.size() * sizeof(double)) == 0;
    };
    return eq(energy, o.energy) && eq(dissipation, o.dissipation) && eq(power, o.power) &&
           eq(shell_energy, o.shell_energy) && eq(recorded, o.recorded) &&
           eq(final_states, o.final_states) && status == o.status && failure == o.failure;
  }
  std::vector<double> energy, dissipation, power, shell_energy, recorded, final_states;
  std::vector<int> status;
  std::vector<long long> failure;
};

void test_ensemble() {
  const int shells = 12;
  const long long members = 7, steps = 2000, stride = 200, samples = steps / stride + 1;
  const int record = 3;
  const Setup s = make_setup(shells, 1.0e-4, 0.005, 0.005);
  const sabra::Model model = model_of(s);
  const std::vector<double> base = random_state(shells, 5u, 0.2);
  std::vector<double> perturbations(2 * shells * members, 0.0);
  std::mt19937_64 rng(11u);
  std::normal_distribution<double> normal(0.0, 1e-6);
  for (long long m = 0; m < members; ++m) {
    for (int j = 8; j < shells; ++j) {
      perturbations[2 * (m * shells + j)] = normal(rng);
      perturbations[2 * (m * shells + j) + 1] = normal(rng);
    }
  }
  perturbations[2 * (4 * shells + 10)] = 1e200;  // member 4 overflows

  EnsembleBuffers one(members, samples, shells, record), many(members, samples, shells, record);
  sabra::run_ensemble(model, base.data(), perturbations.data(), members, 1e-5, steps, stride,
                      record, 1, one.view());
  sabra::run_ensemble(model, base.data(), perturbations.data(), members, 1e-5, steps, stride,
                      record, 3, many.view());
  check(one.same(many), "ensemble output bitwise independent of thread count");
  check(one.status[4] == sabra::member_nonfinite && one.failure[4] >= 0,
        "overflowing member is marked non-finite");
  bool others = true;
  for (long long m = 0; m < members; ++m) {
    if (m != 4) others = others && one.status[m] == sabra::member_completed && one.failure[m] == -1;
  }
  check(others, "other members complete despite one failure");

  std::vector<double> start(2 * shells);
  for (int j = 0; j < 2 * shells; ++j) start[j] = base[j] + perturbations[2 * 2 * shells + j];
  const auto single = integrate(model, start, 1e-5, steps);
  check(std::memcmp(single.data(), &one.final_states[2 * 2 * shells], single.size() * sizeof(double)) == 0,
        "ensemble member equals single integration bitwise");
}

void test_invalid_arguments() {
  const Setup s = make_setup(5, 1e-3, 0.0, 0.0);
  bool threw = false;
  try {
    sabra::make_model(2, s.k.data(), s.nu.data(), s.f.data(), 0.5, -0.5, 2.0);
  } catch (const sabra::InvalidArgument&) {
    threw = true;
  }
  check(threw, "fewer than three shells rejected");
  threw = false;
  try {
    sabra::make_model(5, s.k.data(), s.nu.data(), s.f.data(), 0.5, -0.5, 1.0);
  } catch (const sabra::InvalidArgument&) {
    threw = true;
  }
  check(threw, "shell_ratio <= 1 rejected");
  const sabra::Model model = model_of(s);
  std::vector<double> state(10, 0.1), out(10);
  state[3] = std::nan("");
  threw = false;
  try {
    sabra::evaluate_rhs(model, state.data(), out.data());
  } catch (const sabra::NonFinite&) {
    threw = true;
  }
  check(threw, "non-finite state rejected");
}

}  // namespace

int main() {
  test_rhs_against_reference();
  test_nonlinear_energy_cancellation();
  test_rk4_fourth_order();
  test_fixed_and_generic_kernels_bitwise();
  test_ensemble();
  test_invalid_arguments();
  if (failures) {
    std::printf("%d native check(s) failed\n", failures);
    return EXIT_FAILURE;
  }
  std::printf("all native checks passed\n");
  return EXIT_SUCCESS;
}
