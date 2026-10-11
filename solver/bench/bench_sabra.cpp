// Throughput of the fused Sabra core.
//
// B1: integration only, N=22, nu=3e-8, dt=1e-5.
// B2: sampled diagnostics, N=14, nu=6.104e-5, dt=1e-5, stride 1000.
// The initial state uses K41 magnitudes and deterministic phases; it is a
// throughput fixture, not the seeded scientific initial condition.

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "sabra/sabra.hpp"

namespace {

struct Config {
  int shells;
  double viscosity;
  double energy;
};

sabra::Model build(const Config& config, std::vector<double>& initial) {
  std::vector<double> k(config.shells), nu(config.shells), f(2 * config.shells, 0.0);
  for (int j = 0; j < config.shells; ++j) {
    k[j] = 0.05 * std::pow(2.0, j + 1);
    nu[j] = config.viscosity * k[j] * k[j];
  }
  f[0] = 0.005;
  f[1] = 0.005;
  initial.assign(2 * config.shells, 0.0);
  double total = 0.0;
  for (int j = 0; j < config.shells; ++j) {
    const double magnitude = std::pow(k[j] / k[0], -1.0 / 3.0);
    const double phase = 2.0 * M_PI * std::fmod(0.6180339887498949 * (j + 1), 1.0);
    initial[2 * j] = magnitude * std::cos(phase);
    initial[2 * j + 1] = magnitude * std::sin(phase);
    total += 0.5 * magnitude * magnitude;
  }
  for (double& value : initial) value *= std::sqrt(config.energy / total);
  return sabra::make_model(config.shells, k.data(), nu.data(), f.data(), 0.5, -0.5, 2.0);
}

double median(std::vector<double> values) {
  std::sort(values.begin(), values.end());
  return values[values.size() / 2];
}

double seconds_since(std::chrono::steady_clock::time_point start) {
  return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
}

}  // namespace

int main(int argc, char** argv) {
  const long long b1_steps = argc > 1 ? std::atoll(argv[1]) : 5'000'000;
  const long long b2_steps = argc > 2 ? std::atoll(argv[2]) : 20'000'000;
  const int repeats = 5;

  {
    std::vector<double> initial;
    const sabra::Model model = build({22, 3.0e-8, 0.33}, initial);
    sabra::Workspace w(model.shells);
    w.load(initial.data(), model.shells);
    const sabra::StepSizes h(1.0e-5);
    sabra::dispatch(model, [&](auto count) { sabra::advance(model, count, h, 2000, w); });
    std::vector<double> warmed(2 * model.shells);
    w.store(warmed.data(), model.shells);
    std::vector<double> rates;
    for (int r = 0; r < repeats; ++r) {
      w.load(warmed.data(), model.shells);
      const auto start = std::chrono::steady_clock::now();
      sabra::dispatch(model, [&](auto count) { sabra::advance(model, count, h, b1_steps, w); });
      rates.push_back(b1_steps / seconds_since(start));
      if (!std::isfinite(w.ur[sabra::kGhost])) return EXIT_FAILURE;
    }
    const double rate = median(rates);
    std::printf("B1 integration N=22: %.1f steps/s, %.4f us/step (median of %d x %lld)\n", rate,
                1e6 / rate, repeats, b1_steps);
  }
  {
    std::vector<double> initial;
    const sabra::Model model = build({14, 6.104e-5, 0.32}, initial);
    const long long stride = 1000, samples = b2_steps / stride + 1;
    std::vector<double> energy(samples), dissipation(samples), power(samples),
        shell_energy(samples * model.shells), burn(2 * model.shells), final_state(2 * model.shells);
    sabra::SampledOutput out;
    out.energy = energy.data();
    out.dissipation = dissipation.data();
    out.power_input = power.data();
    out.shell_energy = shell_energy.data();
    out.burn_in_state = burn.data();
    out.final_state = final_state.data();
    std::vector<double> rates;
    for (int r = 0; r < repeats; ++r) {
      const auto start = std::chrono::steady_clock::now();
      sabra::run_sampled(model, initial.data(), 1.0e-5, b2_steps, 0, stride, 0, nullptr, nullptr,
                         out);
      rates.push_back(b2_steps / seconds_since(start));
    }
    const double rate = median(rates);
    std::printf("B2 sampled N=14 stride=1000: %.1f steps/s, %.4f us/step (median of %d x %lld)\n",
                rate, 1e6 / rate, repeats, b2_steps);
  }
  return EXIT_SUCCESS;
}
