import Research.STPR.FiniteShell

noncomputable section
namespace Research.STPR
open Complex BigOperators

/-- Finite sum of the exact quadratic RK4 defect over all shell coordinates. -/
theorem finite_stage_energy_defect {ι : Type*} [Fintype ι]
    (u a b c d : ι → ℂ) (h : ℝ) :
    energy (fun i => u i + (h : ℂ) * stageAverage (a i) (b i) (c i) (d i)) - energy u -
      h * (totalPower u a / 6 + totalPower (u + (h / 2) • a) b / 3 +
        totalPower (u + (h / 2) • b) c / 3 + totalPower (u + h • c) d / 6) =
      h ^ 2 * (energy (fun i => stageAverage (a i) (b i) (c i) (d i)) -
        (totalPower a b + totalPower b c + totalPower c d) / 6) := by
  have hs :
      (∑ i, (energyOne (u i + (h : ℂ) * stageAverage (a i) (b i) (c i) (d i)) - energyOne (u i) -
        h * (power (u i) (a i) / 6 + power (u i + (h / 2 : ℝ) * a i) (b i) / 3 +
          power (u i + (h / 2 : ℝ) * b i) (c i) / 3 + power (u i + (h : ℂ) * c i) (d i) / 6))) =
      ∑ i, h ^ 2 * (energyOne (stageAverage (a i) (b i) (c i) (d i)) -
        (power (a i) (b i) + power (b i) (c i) + power (c i) (d i)) / 6) :=
    Finset.sum_congr rfl (fun i _ => rk4_energy_defect (u i) (a i) (b i) (c i) (d i) h)
  have sum_div (f : ι → ℝ) (q : ℝ) : (∑ i, f i / q) = (∑ i, f i) / q := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  simpa only [energy, totalPower, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_div, ← Finset.mul_sum, Pi.add_apply, Pi.smul_apply, Complex.real_smul] using hs

/-- Stage average agrees with the actual final RK4 linear combination. -/
theorem rk4_as_coordinate_update {ι : Type*} (F : (ι → ℂ) → (ι → ℂ)) (h : ℝ) (u : ι → ℂ) :
    rk4 F h u =
      let a := F u
      let b := F (u + (h / 2) • a)
      let c := F (u + (h / 2) • b)
      let d := F (u + h • c)
      fun i => u i + (h : ℂ) * stageAverage (a i) (b i) (c i) (d i) := by
  ext i
  simp only [rk4, stageAverage, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  push_cast
  ring

/-- The actual RK4 finite-state map has this defect, even when all stage powers vanish. -/
theorem actual_rk4_energy_defect {ι : Type*} [Fintype ι]
    (F : (ι → ℂ) → (ι → ℂ)) (h : ℝ) (u : ι → ℂ) :
    let a := F u
    let b := F (u + (h / 2) • a)
    let c := F (u + (h / 2) • b)
    let d := F (u + h • c)
    energy (rk4 F h u) - energy u -
      h * (totalPower u a / 6 + totalPower (u + (h / 2) • a) b / 3 +
        totalPower (u + (h / 2) • b) c / 3 + totalPower (u + h • c) d / 6) =
      h ^ 2 * (energy (fun i => stageAverage (a i) (b i) (c i) (d i)) -
        (totalPower a b + totalPower b c + totalPower c d) / 6) := by
  dsimp only
  rw [rk4_as_coordinate_update]
  exact finite_stage_energy_defect u _ _ _ _ h

end Research.STPR
