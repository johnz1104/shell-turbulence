import Research.STPR.FiniteShell
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Positivity

noncomputable section
namespace Research.STPR
open Complex BigOperators

/-- The source Euclidean norm, explicitly distinct from the supremum norm on Pi. -/
def stateNorm {ι : Type*} [Fintype ι] (u : ι → ℂ) : ℝ := Real.sqrt (2 * energy u)

/-- Observed components are replaced by the master: their differences become zero. -/
def transverseProjection {ι : Type*} [DecidableEq ι] (observed : Finset ι)
    (u : ι → ℂ) : ι → ℂ := fun i => if i ∈ observed then 0 else u i

theorem energyOne_nonneg (z : ℂ) : 0 ≤ energyOne z := by
  unfold energyOne
  positivity

theorem transverse_energy_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (observed : Finset ι) (u : ι → ℂ) :
    energy (transverseProjection observed u) ≤ energy u := by
  unfold energy
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ observed
  · simp only [transverseProjection, if_pos hi]
    simpa [energyOne] using energyOne_nonneg (u i)
  · simp only [transverseProjection, if_neg hi, le_refl]

theorem transverse_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (observed : Finset ι) (u : ι → ℂ) :
    stateNorm (transverseProjection observed u) ≤ stateNorm u := by
  unfold stateNorm
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (transverse_energy_le observed u) (by norm_num)

/-- The real-valued FTLE is used only under explicit positive-time/norm premises. -/
def finiteTimeExponent (T initial final : ℝ) : ℝ := Real.log (final / initial) / T

theorem finiteTimeExponent_pos_iff (T initial final : ℝ)
    (hT : 0 < T) (hi : 0 < initial) (hf : 0 < final) :
    0 < finiteTimeExponent T initial final ↔ initial < final := by
  unfold finiteTimeExponent
  rw [div_pos_iff_of_pos_right hT, Real.log_pos_iff (div_pos hf hi).le]
  exact (one_lt_div hi)

/-- An independently justified exponential norm bound yields an FTLE upper bound. -/
theorem finiteTimeExponent_le (T initial final L : ℝ)
    (hT : 0 < T) (hi : 0 < initial) (hf : 0 < final)
    (hbound : final ≤ Real.exp (L * T) * initial) :
    finiteTimeExponent T initial final ≤ L := by
  unfold finiteTimeExponent
  apply (div_le_iff₀ hT).2
  apply (Real.log_le_iff_le_exp (div_pos hf hi)).2
  exact (div_le_iff₀ hi).2 hbound

/-- Renormalization log accumulation is exact once multiplicative stretch is justified. -/
theorem stretch_log_product {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 < g i) :
    Real.log (∏ i ∈ s, g i) = ∑ i ∈ s, Real.log (g i) :=
  Real.log_prod (fun i hi => ne_of_gt (hg i hi))

/-- Consecutive strictly positive norms telescope, including all time windows. -/
theorem norm_ratio_log_telescope (r : ℕ → ℝ) (n : ℕ)
    (hr : ∀ j ≤ n, 0 < r j) :
    (∑ j ∈ Finset.range n, Real.log (r (j + 1) / r j)) = Real.log (r n / r 0) := by
  induction n with
  | zero => simp [ne_of_gt (hr 0 (by omega))]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (fun j hj => hr j (by omega))]
    rw [Real.log_div (ne_of_gt (hr n (by omega))) (ne_of_gt (hr 0 (by omega))),
      Real.log_div (ne_of_gt (hr (n + 1) (by omega))) (ne_of_gt (hr n (by omega))),
      Real.log_div (ne_of_gt (hr (n + 1) (by omega))) (ne_of_gt (hr 0 (by omega)))]
    ring

/-- A finite probability law represented by exact normalized masses. -/
def twoPointMean (p a b : ℝ) : ℝ := p * a + (1 - p) * b

def twoPointPositiveMass (p a b : ℝ) : ℝ :=
  (if 0 < a then p else 0) + (if 0 < b then 1 - p else 0)

/-- Negative mean and positive finite-time tail coexist in a certified two-point law. -/
theorem negative_mean_positive_tail :
    (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 ∧
    twoPointMean (1 / 2) 1 (-2) = -1 / 2 ∧
    twoPointPositiveMass (1 / 2) 1 (-2) = 1 / 2 := by
  norm_num [twoPointMean, twoPointPositiveMass]

/-- Deterministic block mean and unnormalized sample variance. -/
def blockMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

def sampleVarianceNumerator {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, (x i - blockMean x) ^ 2

theorem blockMean_constant (n : ℕ) (hn : 0 < n) (c : ℝ) :
    blockMean (fun _ : Fin n => c) = c := by
  unfold blockMean
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

/-- Perfectly correlated observations produce zero empirical variance for any block count. -/
theorem constant_blocks_zero_sampleVariance (n : ℕ) (hn : 0 < n) (c : ℝ) :
    sampleVarianceNumerator (fun _ : Fin n => c) = 0 := by
  simp [sampleVarianceNumerator, blockMean_constant n hn c]

/-- Yet the common ±1 random block mean has population variance one. -/
theorem correlated_blocks_population_variance (n : ℕ) (hn : 0 < n) :
    ((blockMean (fun _ : Fin n => (1 : ℝ))) ^ 2 +
      (blockMean (fun _ : Fin n => (-1 : ℝ))) ^ 2) / 2 = 1 := by
  rw [blockMean_constant n hn 1, blockMean_constant n hn (-1)]
  norm_num

end Research.STPR
