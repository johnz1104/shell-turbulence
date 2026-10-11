import Research.STPR.FiniteShell

noncomputable section
namespace Research.STPR
open Complex BigOperators

/-- Collapse the single possible triad at a given shell and index offset. -/
theorem shifted_delta_sum (N offset i : ℕ) (A : Fin N → ℂ) :
    (∑ t : Fin N, if i = t.val + offset then A t else 0) =
      if h : offset ≤ i ∧ i - offset < N then A ⟨i - offset, h.2⟩ else 0 := by
  by_cases h : offset ≤ i ∧ i - offset < N
  · rw [dif_pos h]
    rw [Finset.sum_eq_single (⟨i - offset, h.2⟩ : Fin N)]
    · simp [Nat.sub_add_cancel h.1]
    · intro j _ hj
      apply if_neg
      intro hij
      apply hj
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    intro hij
    apply h
    constructor <;> omega

/-- Local form with explicit valid-triad branches. Indices are zero-based here;
left/middle/right states therefore have array indices j,j+1,j+2. -/
def localNonlinear {N : ℕ} (b c : ℝ) (k : Fin N → ℝ)
    (u : Fin (N + 2) → ℂ) (i : Fin (N + 2)) : ℂ :=
  (if h : i.val < N then
    triadFirst (k ⟨i.val, h⟩) (u (middleShell ⟨i.val, h⟩)) (u (rightShell ⟨i.val, h⟩)) else 0) +
  (if h : 1 ≤ i.val ∧ i.val - 1 < N then
    triadMiddle b (k ⟨i.val - 1, h.2⟩) (u (leftShell ⟨i.val - 1, h.2⟩))
      (u (rightShell ⟨i.val - 1, h.2⟩)) else 0) +
  (if h : 2 ≤ i.val ∧ i.val - 2 < N then
    triadLast c (k ⟨i.val - 2, h.2⟩) (u (leftShell ⟨i.val - 2, h.2⟩))
      (u (middleShell ⟨i.val - 2, h.2⟩)) else 0)

/-- The triad assembly equals its explicit indexed equation at every finite shell. -/
theorem finiteNonlinear_eq_local {N : ℕ} (b c : ℝ) (k : Fin N → ℝ)
    (u : Fin (N + 2) → ℂ) (i : Fin (N + 2)) :
    finiteNonlinear b c k u i = localNonlinear b c k u i := by
  unfold finiteNonlinear assembledNonlinear triadVector localNonlinear
  simp only [Finset.sum_add_distrib]
  have leftEq (t : Fin N) : (i = leftShell t) ↔ i.val = t.val + 0 := by
    simp [Fin.ext_iff, leftShell]
  have middleEq (t : Fin N) : (i = middleShell t) ↔ i.val = t.val + 1 := by
    simp [Fin.ext_iff, middleShell]
  have rightEq (t : Fin N) : (i = rightShell t) ↔ i.val = t.val + 2 := by
    simp [Fin.ext_iff, rightShell, Nat.add_assoc]
  simp only [leftEq, middleEq, rightEq]
  rw [shifted_delta_sum, shifted_delta_sum, shifted_delta_sum]
  simp

/-- The branches are precisely the Cython source's physical-boundary tests. -/
theorem branch_conditions {N : ℕ} (i : Fin (N + 2)) :
    (i.val < N ↔ i.val + 2 < N + 2) ∧
    (1 ≤ i.val ∧ i.val - 1 < N ↔ 0 < i.val ∧ i.val + 1 < N + 2) ∧
    (2 ≤ i.val ∧ i.val - 2 < N ↔ 1 < i.val) := by
  constructor
  · omega
  · constructor <;> omega

/-- Values outside the represented array are literal zero ghost shells. -/
def ghost {N : ℕ} (u : Fin N → ℂ) (j : ℤ) : ℂ :=
  if h : 0 ≤ j ∧ j < N then u ⟨j.toNat, by omega⟩ else 0

theorem ghost_outside {N : ℕ} (u : Fin N → ℂ) (j : ℤ)
    (hj : j < 0 ∨ N ≤ j) : ghost u j = 0 := by
  unfold ghost
  apply dif_neg
  omega

theorem ghost_inside {N : ℕ} (u : Fin N → ℂ) (i : Fin N) : ghost u i.val = u i := by
  unfold ghost
  have h : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < N := by constructor <;> omega
  rw [dif_pos h]
  congr

end Research.STPR
