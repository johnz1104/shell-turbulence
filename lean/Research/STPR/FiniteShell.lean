import Research.STPR.RK4
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Module.Pi

noncomputable section
namespace Research.STPR
open Complex BigOperators

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]

/-- Sum of per-shell kinetic energies, in the source's normalization. -/
def energy (u : ι → ℂ) : ℝ := ∑ i, energyOne (u i)

/-- Real Hermitian pairing on the finite state. -/
def totalPower (u v : ι → ℂ) : ℝ := ∑ i, power (u i) (v i)

theorem power_add_right (u v w : ℂ) : power u (v + w) = power u v + power u w := by
  simp [power, mul_add]

theorem power_sum_right (u : ℂ) (v : τ → ℂ) :
    power u (∑ t, v t) = ∑ t, power u (v t) := by
  unfold power
  rw [Finset.mul_sum]
  exact map_sum Complex.reAddGroupHom _ _

theorem totalPower_delta (u : ι → ℂ) (j : ι) (a : ℂ) :
    (∑ i, power (u i) (if i = j then a else 0)) = power (u j) a := by
  simp [power, mul_ite, apply_ite]

/-- One triad deposited into its three shell coordinates; no wraparound. -/
def triadVector (left middle right : τ → ι) (b c : ℝ) (k : τ → ℝ)
    (u : ι → ℂ) (t : τ) (i : ι) : ℂ :=
  (if i = left t then triadFirst (k t) (u (middle t)) (u (right t)) else 0) +
  (if i = middle t then triadMiddle b (k t) (u (left t)) (u (right t)) else 0) +
  (if i = right t then triadLast c (k t) (u (left t)) (u (middle t)) else 0)

/-- The finite nonlinear field assembled by represented consecutive triads. -/
def assembledNonlinear (left middle right : τ → ι) (b c : ℝ) (k : τ → ℝ)
    (u : ι → ℂ) (i : ι) : ℂ := ∑ t, triadVector left middle right b c k u t i

/-- Finite assembly preserves the exact local energy cancellation. -/
theorem assembled_energy_cancellation (left middle right : τ → ι)
    (b : ℝ) (k : τ → ℝ) (u : ι → ℂ) :
    totalPower u (assembledNonlinear left middle right b (b - 1) k u) = 0 := by
  unfold totalPower assembledNonlinear
  simp only [power_sum_right]
  rw [Finset.sum_comm]
  simp only [triadVector, power_add_right, Finset.sum_add_distrib,
    totalPower_delta, triad_energy_cancellation, Finset.sum_const_zero]

/-- Weighted local recurrences suffice after finite assembly too. -/
theorem assembled_weighted_cancellation (left middle right : τ → ι)
    (b c : ℝ) (k : τ → ℝ) (u : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ t, w (left t) - b * w (middle t) + c * w (right t) = 0) :
    (∑ i, w i * power (u i) (assembledNonlinear left middle right b c k u i)) = 0 := by
  unfold assembledNonlinear
  simp only [power_sum_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro t _
  simp only [triadVector, power_add_right, mul_add, Finset.sum_add_distrib]
  have delta (j : ι) (a : ℂ) :
      (∑ i, w i * power (u i) (if i = j then a else 0)) = w j * power (u j) a := by
    simp [power, mul_ite, apply_ite]
  rw [delta, delta, delta]
  exact triad_weighted_cancellation b c (k t) _ _ _ _ _ _ (hw t)

/-- Shell phase multiplication as an actual real-linear map. -/
def phaseMap (p : ι → ℂ) : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) where
  toFun u i := p i * u i
  map_add' u v := by ext i; simp [mul_add]
  map_smul' a u := by
    ext i
    change p i * ((a : ℂ) * u i) = (a : ℂ) * (p i * u i)
    ring

theorem triadVector_equivariance (left middle right : τ → ι)
    (b c : ℝ) (k : τ → ℝ) (p u : ι → ℂ)
    (hp : ∀ i, UnitPhase (p i))
    (hrec : ∀ t, p (right t) = p (left t) * p (middle t)) (t : τ) (i : ι) :
    triadVector left middle right b c k (phaseMap p u) t i =
      p i * triadVector left middle right b c k u t i := by
  unfold triadVector
  simp only [phaseMap, LinearMap.coe_mk, AddHom.coe_mk]
  have ha :
      (if i = left t then triadFirst (k t) (p (middle t) * u (middle t))
        (p (right t) * u (right t)) else 0) =
      p i * (if i = left t then triadFirst (k t) (u (middle t)) (u (right t)) else 0) := by
    by_cases h : i = left t
    · subst i
      simp only [if_pos rfl]
      rw [hrec t, triad_first_equivariance _ _ _ _ _ (hp (middle t))]
      simp
    · simp only [if_neg h, mul_zero]
  have hb :
      (if i = middle t then triadMiddle b (k t) (p (left t) * u (left t))
        (p (right t) * u (right t)) else 0) =
      p i * (if i = middle t then triadMiddle b (k t) (u (left t)) (u (right t)) else 0) := by
    by_cases h : i = middle t
    · subst i
      simp only [if_pos rfl]
      rw [hrec t, triad_middle_equivariance _ _ _ _ _ _ (hp (left t))]
      simp
    · simp only [if_neg h, mul_zero]
  have hc :
      (if i = right t then triadLast c (k t) (p (left t) * u (left t))
        (p (middle t) * u (middle t)) else 0) =
      p i * (if i = right t then triadLast c (k t) (u (left t)) (u (middle t)) else 0) := by
    by_cases h : i = right t
    · subst i
      simp only [if_pos rfl]
      rw [triad_last_equivariance, hrec t]
      simp
    · simp only [if_neg h, mul_zero]
  rw [ha, hb, hc]
  ring

theorem assembled_equivariance (left middle right : τ → ι)
    (b c : ℝ) (k : τ → ℝ) (p u : ι → ℂ)
    (hp : ∀ i, UnitPhase (p i))
    (hrec : ∀ t, p (right t) = p (left t) * p (middle t)) :
    assembledNonlinear left middle right b c k (phaseMap p u) =
      phaseMap p (assembledNonlinear left middle right b c k u) := by
  ext i
  simp only [assembledNonlinear, triadVector_equivariance left middle right b c k p u hp hrec]
  simp [phaseMap, assembledNonlinear, Finset.mul_sum]

theorem phase_energy (p u : ι → ℂ) (hp : ∀ i, UnitPhase (p i)) :
    energy (phaseMap p u) = energy u := by
  unfold energy
  apply Finset.sum_congr rfl
  intro i _
  exact phase_energyOne (p i) (u i) (hp i)

theorem phase_totalPower (p u v : ι → ℂ) (hp : ∀ i, UnitPhase (p i)) :
    totalPower (phaseMap p u) (phaseMap p v) = totalPower u v := by
  unfold totalPower
  apply Finset.sum_congr rfl
  intro i _
  exact phase_power (p i) (u i) (v i) (hp i)

/-- Complete fixed-forcing finite vector field. Rates are nu*k_n^2 in Sabra. -/
def fullRHS (N : (ι → ℂ) → (ι → ℂ)) (rate : ι → ℝ) (forcing u : ι → ℂ) : ι → ℂ :=
  fun i => N u i - (rate i : ℂ) * u i + forcing i

/-- The full finite power balance is now an all-state theorem. -/
theorem finite_power_balance (left middle right : τ → ι)
    (b : ℝ) (k : τ → ℝ) (rate : ι → ℝ) (f u : ι → ℂ) :
    totalPower u (fullRHS (assembledNonlinear left middle right b (b - 1) k) rate f u) =
      totalPower u f - ∑ i, 2 * rate i * energyOne (u i) := by
  simp only [totalPower, fullRHS, forced_viscous_power, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have hn := assembled_energy_cancellation left middle right b k u
  unfold totalPower at hn
  rw [hn]
  ring

/-- Full state and forcing must transform jointly. -/
theorem fullRHS_equivariance (left middle right : τ → ι)
    (b c : ℝ) (k : τ → ℝ) (rate : ι → ℝ) (p f u : ι → ℂ)
    (hp : ∀ i, UnitPhase (p i))
    (hrec : ∀ t, p (right t) = p (left t) * p (middle t)) :
    fullRHS (assembledNonlinear left middle right b c k) rate (phaseMap p f) (phaseMap p u) =
      phaseMap p (fullRHS (assembledNonlinear left middle right b c k) rate f u) := by
  unfold fullRHS
  rw [assembled_equivariance left middle right b c k p u hp hrec]
  ext i
  simp only [phaseMap, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- The actual complete shell RHS, including viscosity and force, has RK4 covariance. -/
theorem shell_rk4_equivariance (left middle right : τ → ι)
    (b c : ℝ) (k : τ → ℝ) (rate : ι → ℝ) (p f u : ι → ℂ)
    (hp : ∀ i, UnitPhase (p i))
    (hrec : ∀ t, p (right t) = p (left t) * p (middle t)) (h : ℝ) :
    phaseMap p (rk4 (fullRHS (assembledNonlinear left middle right b c k) rate f) h u) =
      rk4 (fullRHS (assembledNonlinear left middle right b c k) rate (phaseMap p f)) h
        (phaseMap p u) := by
  apply rk4_equivariance
  intro x
  exact (fullRHS_equivariance left middle right b c k rate p f x hp hrec).symm

/-- The two ghost shells on each side leave N represented triads in N+2 shells. -/
def leftShell {N : ℕ} (t : Fin N) : Fin (N + 2) := Fin.castAdd 2 t
def middleShell {N : ℕ} (t : Fin N) : Fin (N + 2) := t.succ.castSucc
def rightShell {N : ℕ} (t : Fin N) : Fin (N + 2) := t.succ.succ

/-- Specialization to the consecutive finite Sabra shell graph. -/
def finiteNonlinear {N : ℕ} (b c : ℝ) (k : Fin N → ℝ)
    (u : Fin (N + 2) → ℂ) : Fin (N + 2) → ℂ :=
  assembledNonlinear leftShell middleShell rightShell b c k u

theorem finite_nonlinear_energy {N : ℕ} (b : ℝ) (k : Fin N → ℝ)
    (u : Fin (N + 2) → ℂ) : totalPower u (finiteNonlinear b (b - 1) k u) = 0 :=
  assembled_energy_cancellation leftShell middleShell rightShell b k u

end Research.STPR
