# Lean proofs

These are machine-checked statements, in exact real arithmetic, about the
equation and the time step that the solver in [`../solver`](../solver)
evaluates. They are written in Lean 4 with mathlib, both at `v4.33.1`, pinned in
`lean-toolchain` and `lake-manifest.json`. They contain no `sorry`, `admit` or
added axioms.

```sh
cd lean
lake exe cache get   # downloads prebuilt mathlib (several GB)
lake build
```

## How the proofs relate to the solver

- **Exact arithmetic only.** The proofs work with exact real and complex
  numbers. The solver uses IEEE double precision, and nothing here bounds its
  rounding error.
- **Reference implementations.** The files were written against reference
  implementations in the research project this repository comes from: NumPy
  `sabra.py` and `integration.py`, and an earlier Cython kernel. Some docstrings
  cite those files by line number.
- **Same expressions as the C++.** The C++ solver evaluates the same
  expressions. In [`sabra.hpp`](../solver/include/sabra/sabra.hpp), `rhs()` is
  `ghostNonlinear` plus viscosity and forcing, and `rk4_step()` is `rk4`. That
  correspondence was checked numerically, to round-off, not proved.
- **Indexing.** Arrays are zero-based: index 0 is shell 1, and
  `wavenumber k₀ q n = k₀ q^(n+1)`. A chain of `N + 2` shells has `N`
  interacting triads.
- **Module paths.** The paths keep the original project's `Research.STPR`
  prefix. `Research.lean` imports all ten.

## Files

Listed in dependency order.

**`Algebra.lean`**
- Defines the three terms a triad of consecutive shells contributes:
  `triadFirst`, `triadMiddle` and `triadLast`.
- With `c = b − 1`, their energy contributions cancel exactly
  (`triad_energy_cancellation`).
- With `b = 1/2`, a helicity-like weighted sum cancels too
  (`helicity_triad_cancellation`).
- Each term transforms consistently under phase rotations.

**`FiniteShell.lean`**
- Assembles the triads over a finite chain (`finiteNonlinear`) and proves that
  the nonlinear term conserves total energy for every state
  (`assembled_energy_cancellation`).
- Defines the full right-hand side, nonlinearity − νk²u + f (`fullRHS`).
- Proves the energy balance, rate of change = power input − dissipation, as an
  exact identity (`finite_power_balance`).
- Phase symmetry carries through the right-hand side and through a whole RK4
  step (`shell_rk4_equivariance`).

**`Correspondence.lean`**
- The assembled term equals the shell-by-shell formula with explicit boundary
  branches (`finiteNonlinear_eq_local`).
- Those branches are exactly the array-bounds tests (`branch_conditions`).
- Defines zero padding outside the array (`ghost`).

**`Growth.lean`**
- Supporting definitions: a state norm, a projection that zeroes chosen shells,
  and a finite-time growth rate.
- A two-point example with growth rates +1 and −2, each with probability ½. Its
  mean growth is negative, yet half of the probability is on positive growth
  (`negative_mean_positive_tail`).
- It is included only because `PhaseConstruction` imports it; the solver does
  not use it.

**`PhaseConstruction.lean`**
- Defines the geometric wavenumbers and proves the identities
  `k_n / q = k_{n−1}` and `k_n / q² = k_{n−2}` that the solver relies on
  (`wavenumber_div_ratio`, `wavenumber_div_ratio_squared`).
- Builds the family of shell-by-shell phase rotations that leave the equations
  unchanged.
- Shows that the solver's default forcing (1 + i)/200 is a phase rotation of
  the real forcing √2/200 (`printed_force_to_positive_real`).

**`GhostEquation.lean`**
- `ghostNonlinear` is the zero-padded array formula the solver evaluates: both
  complex conjugations, the `k/q` and `k/q²` factors, and two zero shells at
  each end.
- `finiteNonlinear_eq_ghost` proves it equals the triad model at every shell,
  for any `q ≠ 0`.

**`Diagnostics.lean`**
- Helicity cancels over the whole chain for `q = 2`, `b = 1/2`.
- The dissipation diagnostic, Σ ν k² |u|², is non-negative and unchanged by
  phase rotations.
- The zero-padded formula conserves energy (`ghost_nonlinear_energy`).

**`RK4.lean`**
- Defines the classical RK4 map (`rk4`), with stage weights 1, 2, 2, 1 over 6.
- Gives an exact one-coordinate formula for a step's energy change: the stage
  power terms plus an `h²` remainder (`rk4_energy_defect`).
- For the oscillator u′ = iωu, RK4 multiplies the energy by
  1 + x⁶(x² − 8)/576, where x = hω (`oscillator_energy_defect`).

**`EnergyDefect.lean`**
- Proves the same formula for the full RK4 map, summed over all shells
  (`actual_rk4_energy_defect`).
- So even when every stage's power is zero, a step changes the energy by `h²`
  times an explicit quadratic.

**`Counterexamples.lean`**
- Takes three shells with k = 1, b = 1/2, no viscosity and no forcing, and one
  RK4 step with h = 1 from (1, 0, 1).
- The step lands on an explicit rational state (`sabra_rk4_witness_state`).
- The energy changes by exactly −42254587/77309411328
  (`sabra_rk4_energy_defect_witness`).
- So the solver's time step does not conserve energy exactly, even though the
  equations do.

## Not covered

- rounding-error bounds;
- existence and uniqueness of solutions;
- RK4 error bounds against the exact solution;
- drive/response synchronization and tangent maps.
