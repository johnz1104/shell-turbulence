import Research.STPR.Algebra
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Complex.Module

noncomputable section
namespace Research.STPR
open Complex

/-- The complete classical explicit RK4 map from integration.py:20-27. -/
def rk4 {V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : V → V) (h : ℝ) (u : V) : V :=
  let k₁ := F u
  let k₂ := F (u + (h / 2) • k₁)
  let k₃ := F (u + (h / 2) • k₂)
  let k₄ := F (u + h • k₃)
  u + (h / 6) • (k₁ + (2 : ℝ) • k₂ + (2 : ℝ) • k₃ + k₄)

/-- Linear covariance of the RHS extends to all four actual RK4 stages. -/
theorem rk4_equivariance {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (P : V →ₗ[ℝ] W) (F : V → V) (G : W → W)
    (hFG : ∀ x, P (F x) = G (P x)) (h : ℝ) (u : V) :
    P (rk4 F h u) = rk4 G h (P u) := by
  simp only [rk4, map_add, map_smul, hFG]

/-- Convex average of the four classical RK4 stage derivatives. -/
def stageAverage (a b c d : ℂ) : ℂ :=
  (1 / 6 : ℂ) * (a + 2 * b + 2 * c + d)

/-- Exact scalar-coordinate quadratic energy defect; sum this over shells. -/
theorem rk4_energy_defect (u a b c d : ℂ) (h : ℝ) :
    energyOne (u + (h : ℂ) * stageAverage a b c d) - energyOne u -
      h * (power u a / 6 + power (u + (h / 2 : ℝ) * a) b / 3 +
        power (u + (h / 2 : ℝ) * b) c / 3 + power (u + (h : ℂ) * c) d / 6) =
      h ^ 2 * (energyOne (stageAverage a b c d) -
        (power a b + power b c + power c d) / 6) := by
  norm_num [energyOne, stageAverage, power, Complex.mul_re, Complex.mul_im]
  <;> ring

/-- The algebraic RHS power separates viscosity and forcing before any ODE claim. -/
theorem forced_viscous_power (u n f : ℂ) (rate : ℝ) :
    power u (n - (rate : ℂ) * u + f) =
      power u n - 2 * rate * energyOne u + power u f := by
  simp [power, energyOne, Complex.mul_re, Complex.mul_im]
  <;> ring

/-- RK4 stability polynomial for an imaginary scalar frequency. -/
def oscillatorAmplification (x : ℝ) : ℂ :=
  ⟨1 - x ^ 2 / 2 + x ^ 4 / 24, x - x ^ 3 / 6⟩

/-- The polynomial above is proved to be the actual RK4 map, not a surrogate. -/
theorem rk4_oscillator (omega h : ℝ) (z : ℂ) :
    rk4 (fun w : ℂ => I * (omega : ℂ) * w) h z = oscillatorAmplification (h * omega) * z := by
  apply Complex.ext <;>
    norm_num [rk4, oscillatorAmplification, Complex.smul_re, Complex.smul_im,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The exact defect of the RK4 oscillator polynomial is generally nonzero. -/
theorem oscillator_energy_defect (z : ℂ) (x : ℝ) :
    energyOne (oscillatorAmplification x * z) - energyOne z =
      energyOne z * (x ^ 6 * (x ^ 2 - 8) / 576) := by
  norm_num [energyOne, oscillatorAmplification, Complex.mul_re, Complex.mul_im]
  <;> ring

/-- A concrete exact failure of generic quadratic preservation by this polynomial. -/
theorem oscillator_nonconservation :
    energyOne (oscillatorAmplification 1) - energyOne 1 = -(7 / 1152 : ℝ) := by
  norm_num [energyOne, oscillatorAmplification, Complex.mul_re, Complex.mul_im]

end Research.STPR
