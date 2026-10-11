import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Exact-real algebra for the implemented Li-convention Sabra triad.
No floating-point correspondence, time-integrator accuracy, or ODE existence
is asserted by these algebraic theorems. -/
noncomputable section
namespace Research.STPR
open Complex

/-- Real part of the Hermitian pairing on one complex coordinate. -/
def power (x y : ℂ) : ℝ := (star x * y).re

/-- Half the squared modulus, in real coordinates. -/
def energyOne (x : ℂ) : ℝ := (x.re ^ 2 + x.im ^ 2) / 2

/-- First, middle, and last contributions from a consecutive shell triad. -/
def triadFirst (k : ℝ) (y z : ℂ) : ℂ := I * (k * z * star y)
def triadMiddle (b k : ℝ) (x z : ℂ) : ℂ := I * (-(b : ℂ) * k * z * star x)
def triadLast (c k : ℝ) (x y : ℂ) : ℂ := I * (-(c : ℂ) * k * y * x)

/-- Weighted triad energy transfer, with the signed coefficient made explicit. -/
theorem weighted_triad_power (b c k w₀ w₁ w₂ : ℝ) (x y z : ℂ) :
    w₀ * power x (triadFirst k y z) +
      w₁ * power y (triadMiddle b k x z) +
      w₂ * power z (triadLast c k x y) =
      (w₀ - b * w₁ + c * w₂) * power x (triadFirst k y z) := by
  simp [power, triadFirst, triadMiddle, triadLast,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im]
  <;> ring

/-- The source's c=b-1 relation cancels triad energy for every state. -/
theorem triad_energy_cancellation (b k : ℝ) (x y z : ℂ) :
    power x (triadFirst k y z) + power y (triadMiddle b k x z) +
      power z (triadLast (b - 1) k x y) = 0 := by
  have h := weighted_triad_power b (b - 1) k 1 1 1 x y z
  simpa using h

/-- General weighted invariant recurrence, including helicity-like weights. -/
theorem triad_weighted_cancellation (b c k w₀ w₁ w₂ : ℝ) (x y z : ℂ)
    (hw : w₀ - b * w₁ + c * w₂ = 0) :
    w₀ * power x (triadFirst k y z) +
      w₁ * power y (triadMiddle b k x z) +
      w₂ * power z (triadLast c k x y) = 0 := by
  rw [weighted_triad_power, hw, zero_mul]

theorem helicity_triad_cancellation (k w : ℝ) (x y z : ℂ) :
    w * power x (triadFirst k y z) +
      (-2 * w) * power y (triadMiddle (1 / 2) k x z) +
      (4 * w) * power z (triadLast (-1 / 2) k x y) = 0 := by
  apply triad_weighted_cancellation
  ring

/-- The coefficient condition is nonvacuous. -/
theorem triad_flux_witness : power 1 (triadFirst 1 1 I) = -1 := by
  norm_num [power, triadFirst, Complex.mul_re, Complex.mul_im]

/-- Unit complex multiplier, expressed algebraically. -/
def UnitPhase (p : ℂ) : Prop := p * star p = 1

theorem phase_power (p x y : ℂ) (hp : UnitPhase p) :
    power (p * x) (p * y) = power x y := by
  unfold power UnitPhase at *
  have heq : star (p * x) * (p * y) = star x * y := by
    calc
      star (p * x) * (p * y) = (p * star p) * (star x * y) := by
        simp only [star_mul]
        ring
      _ = star x * y := by rw [hp, one_mul]
  rw [heq]

theorem phase_energyOne (p x : ℂ) (hp : UnitPhase p) :
    energyOne (p * x) = energyOne x := by
  have aux (z : ℂ) : energyOne z = power z z / 2 := by
    simp [energyOne, power, Complex.mul_re]
    <;> ring
  rw [aux, aux, phase_power p x x hp]

/-- On one triad the phase recurrence is p₂=p₀p₁. -/
theorem triad_first_equivariance (k : ℝ) (p q y z : ℂ)
    (hq : UnitPhase q) :
    triadFirst k (q * y) ((p * q) * z) = p * triadFirst k y z := by
  unfold triadFirst UnitPhase at *
  calc
    I * ((k : ℂ) * ((p * q) * z) * star (q * y)) =
      (q * star q) * (p * (I * (k * z * star y))) := by
        simp only [star_mul]
        ring
    _ = p * (I * (k * z * star y)) := by rw [hq, one_mul]

theorem triad_middle_equivariance (b k : ℝ) (p q x z : ℂ)
    (hp : UnitPhase p) :
    triadMiddle b k (p * x) ((p * q) * z) = q * triadMiddle b k x z := by
  unfold triadMiddle UnitPhase at *
  calc
    I * (-(b : ℂ) * k * ((p * q) * z) * star (p * x)) =
      (p * star p) * (q * (I * (-(b : ℂ) * k * z * star x))) := by
        simp only [star_mul]
        ring
    _ = q * (I * (-(b : ℂ) * k * z * star x)) := by rw [hp, one_mul]

theorem triad_last_equivariance (c k : ℝ) (p q x y : ℂ) :
    triadLast c k (p * x) (q * y) = (p * q) * triadLast c k x y := by
  unfold triadLast
  ring

/-- Printed pair versus real-only sensitivity: exact squared magnitudes differ. -/
theorem forcing_magnitude_distinction :
    2 * energyOne ((1 / 200 : ℂ) + (1 / 200 : ℂ) * I) = (1 / 20000 : ℝ) ∧
    2 * energyOne (1 / 200 : ℂ) = (1 / 40000 : ℝ) ∧
    (1 / 20000 : ℝ) ≠ 1 / 40000 := by
  norm_num [energyOne, Complex.mul_re, Complex.mul_im]

/-- Real-linear first variation plus quadratic remainder of conjugated product. -/
theorem conjugate_product_perturbation (x y dx dy : ℂ) :
    (x + dx) * star (y + dy) - x * star y =
      dx * star y + x * star dy + dx * star dy := by
  simp only [star_add]
  ring

theorem product_perturbation (x y dx dy : ℂ) :
    (x + dx) * (y + dy) - x * y = dx * y + x * dy + dx * dy := by
  ring

end Research.STPR
