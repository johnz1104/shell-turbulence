import Research.STPR.GhostEquation

noncomputable section
namespace Research.STPR
open Complex BigOperators

/-- Exactly signed geometric helicity weights in zero-based array indexing. -/
def helicityWeight (k₀ : ℝ) (n : ℕ) : ℝ := (-1) ^ (n + 1) * wavenumber k₀ 2 n

theorem helicity_weight_successor (k₀ : ℝ) (n : ℕ) :
    helicityWeight k₀ (n + 1) = -2 * helicityWeight k₀ n := by
  unfold helicityWeight
  rw [wavenumber_successor]
  simp only [pow_succ]
  ring

theorem finite_helicity_cancellation {N : ℕ} (k₀ : ℝ) (u : Fin (N + 2) → ℂ) :
    (∑ i, helicityWeight k₀ i.val * power (u i)
      (finiteNonlinear (1 / 2) (-1 / 2) (fun t : Fin N => wavenumber k₀ 2 t.val) u i)) = 0 := by
  apply assembled_weighted_cancellation
  intro t
  change helicityWeight k₀ t.val - 1 / 2 * helicityWeight k₀ (t.val + 1) +
    (-1 / 2) * helicityWeight k₀ (t.val + 1 + 1) = 0
  rw [helicity_weight_successor, helicity_weight_successor, helicity_weight_successor]
  ring

/-- Source viscous dissipation expressed in the same exact quadratic normalization. -/
def dissipation {ι : Type*} [Fintype ι] (nu : ℝ) (k : ι → ℝ) (u : ι → ℂ) : ℝ :=
  ∑ i, 2 * nu * k i ^ 2 * energyOne (u i)

theorem dissipation_nonneg {ι : Type*} [Fintype ι]
    (nu : ℝ) (k : ι → ℝ) (u : ι → ℂ) (hnu : 0 ≤ nu) : 0 ≤ dissipation nu k u := by
  unfold dissipation
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hnu) (sq_nonneg _)) (energyOne_nonneg _)

theorem phase_dissipation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nu : ℝ) (k : ι → ℝ) (p u : ι → ℂ) (hp : ∀ i, UnitPhase (p i)) :
    dissipation nu k (phaseMap p u) = dissipation nu k u := by
  unfold dissipation
  apply Finset.sum_congr rfl
  intro i _
  rw [show (phaseMap p u) i = p i * u i from rfl, phase_energyOne _ _ (hp i)]

/-- The fully indexed source ghost equation has exact nonlinear energy cancellation. -/
theorem ghost_nonlinear_energy {N : ℕ} (k₀ q b : ℝ) (hq : q ≠ 0)
    (u : Fin (N + 2) → ℂ) :
    totalPower u (ghostNonlinear k₀ q b (b - 1) u) = 0 := by
  have heq : ghostNonlinear k₀ q b (b - 1) u =
      finiteNonlinear b (b - 1) (fun t : Fin N => wavenumber k₀ q t.val) u := by
    ext i
    exact (finiteNonlinear_eq_ghost k₀ q b (b - 1) hq u i).symm
  rw [heq]
  exact finite_nonlinear_energy b _ u

end Research.STPR
