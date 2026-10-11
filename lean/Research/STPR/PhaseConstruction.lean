import Research.STPR.Growth
import Research.STPR.Correspondence

noncomputable section
namespace Research.STPR
open Complex

/-- Array-indexed geometric wavenumbers: index 0 represents physical shell 1. -/
def wavenumber (k₀ q : ℝ) (n : ℕ) : ℝ := k₀ * q ^ (n + 1)

theorem wavenumber_successor (k₀ q : ℝ) (n : ℕ) :
    wavenumber k₀ q (n + 1) = wavenumber k₀ q n * q := by
  simp only [wavenumber, pow_succ]
  ring

/-- Exact-real correspondence to source evaluation k_n/q. -/
theorem wavenumber_div_ratio (k₀ q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    wavenumber k₀ q (n + 1) / q = wavenumber k₀ q n := by
  rw [wavenumber_successor, mul_div_cancel_right₀ _ hq]

/-- Exact-real correspondence to k_n/(q*q); floating evaluations remain separate. -/
theorem wavenumber_div_ratio_squared (k₀ q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    wavenumber k₀ q (n + 2) / (q * q) = wavenumber k₀ q n := by
  rw [show n + 2 = (n + 1) + 1 by omega, wavenumber_successor, wavenumber_successor]
  rw [mul_assoc, mul_div_cancel_right₀ _ (mul_ne_zero hq hq)]

theorem UnitPhase.mul {p q : ℂ} (hp : UnitPhase p) (hq : UnitPhase q) : UnitPhase (p * q) := by
  unfold UnitPhase at *
  calc
    (p * q) * star (p * q) = (p * star p) * (q * star q) := by
      simp only [star_mul]
      ring
    _ = 1 := by rw [hp, hq, one_mul]

/-- Two freely selected unit phases generate the complete nonuniform shell symmetry. -/
def phaseSequence (p q : ℂ) : ℕ → ℂ
  | 0 => p
  | 1 => q
  | n + 2 => phaseSequence p q n * phaseSequence p q (n + 1)

theorem phaseSequence_unit (p q : ℂ) (hp : UnitPhase p) (hq : UnitPhase q) (n : ℕ) :
    UnitPhase (phaseSequence p q n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact hp
  | one => exact hq
  | more n hn hn1 => exact hn.mul hn1

/-- This constructed phase family satisfies every represented finite triad recurrence. -/
theorem phaseSequence_finite_recurrence {N : ℕ} (p q : ℂ) (t : Fin N) :
    phaseSequence p q (rightShell t).val =
      phaseSequence p q (leftShell t).val * phaseSequence p q (middleShell t).val := by
  change phaseSequence p q (t.val + 1 + 1) = phaseSequence p q t.val * phaseSequence p q (t.val + 1)
  rw [show t.val + 1 + 1 = t.val + 2 by omega]
  rfl

/-- A nontrivial unit first-shell phase sends the printed complex force to positive real. -/
def realForcingPhase : ℂ := ⟨Real.sqrt 2 / 2, -(Real.sqrt 2 / 2)⟩

theorem realForcingPhase_unit : UnitPhase realForcingPhase := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold UnitPhase realForcingPhase
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · nlinarith

theorem printed_force_to_positive_real :
    realForcingPhase * ((1 / 200 : ℂ) + (1 / 200 : ℂ) * I) =
      (Real.sqrt 2 / 200 : ℝ) := by
  apply Complex.ext <;> norm_num [realForcingPhase, Complex.mul_re, Complex.mul_im] <;> ring

end Research.STPR
