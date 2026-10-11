import Research.STPR.PhaseConstruction

noncomputable section
namespace Research.STPR
open Complex

/-- This is the exact real-arithmetic array formula implemented in sabra.py:171-174. -/
def ghostNonlinear {N : ℕ} (k₀ q b c : ℝ) (u : Fin (N + 2) → ℂ) (i : Fin (N + 2)) : ℂ :=
  triadFirst (wavenumber k₀ q i.val) (ghost u ((i.val : ℤ) + 1)) (ghost u ((i.val : ℤ) + 2)) +
  triadMiddle b (wavenumber k₀ q i.val / q) (ghost u ((i.val : ℤ) - 1))
    (ghost u ((i.val : ℤ) + 1)) +
  triadLast c (wavenumber k₀ q i.val / (q * q)) (ghost u ((i.val : ℤ) - 2))
    (ghost u ((i.val : ℤ) - 1))

theorem ghost_triad_left {N : ℕ} (u : Fin (N + 2) → ℂ) (t : Fin N) :
    ghost u (t.val : ℤ) = u (leftShell t) := by
  exact ghost_inside u (leftShell t)

theorem ghost_triad_middle {N : ℕ} (u : Fin (N + 2) → ℂ) (t : Fin N) :
    ghost u ((t.val : ℤ) + 1) = u (middleShell t) := by
  simpa [middleShell] using ghost_inside u (middleShell t)

theorem ghost_triad_right {N : ℕ} (u : Fin (N + 2) → ℂ) (t : Fin N) :
    ghost u ((t.val : ℤ) + 2) = u (rightShell t) := by
  simpa [rightShell, add_assoc] using ghost_inside u (rightShell t)

/-- All source indices, both conjugations, the q divisions, and ghost branches
correspond to the finite triad model. q≠0 is essential for the divisions. -/
theorem finiteNonlinear_eq_ghost {N : ℕ} (k₀ q b c : ℝ) (hq : q ≠ 0)
    (u : Fin (N + 2) → ℂ) (i : Fin (N + 2)) :
    finiteNonlinear b c (fun t : Fin N => wavenumber k₀ q t.val) u i =
      ghostNonlinear k₀ q b c u i := by
  rw [finiteNonlinear_eq_local]
  unfold localNonlinear ghostNonlinear
  have hfirst :
      (if h : i.val < N then
        triadFirst (wavenumber k₀ q i.val) (u (middleShell ⟨i.val, h⟩))
          (u (rightShell ⟨i.val, h⟩)) else 0) =
      triadFirst (wavenumber k₀ q i.val) (ghost u ((i.val : ℤ) + 1))
        (ghost u ((i.val : ℤ) + 2)) := by
    by_cases h : i.val < N
    · rw [dif_pos h, ghost_triad_middle u (⟨i.val, h⟩ : Fin N),
        ghost_triad_right u (⟨i.val, h⟩ : Fin N)]
    · rw [dif_neg h]
      have hg : ghost u ((i.val : ℤ) + 2) = 0 := ghost_outside u _ (Or.inr (by omega))
      simp [triadFirst, hg]
  have hmiddle :
      (if h : 1 ≤ i.val ∧ i.val - 1 < N then
        triadMiddle b (wavenumber k₀ q (i.val - 1)) (u (leftShell ⟨i.val - 1, h.2⟩))
          (u (rightShell ⟨i.val - 1, h.2⟩)) else 0) =
      triadMiddle b (wavenumber k₀ q i.val / q) (ghost u ((i.val : ℤ) - 1))
        (ghost u ((i.val : ℤ) + 1)) := by
    by_cases h : 1 ≤ i.val ∧ i.val - 1 < N
    · rw [dif_pos h]
      let t : Fin N := ⟨i.val - 1, h.2⟩
      have hn : i.val = t.val + 1 := by dsimp [t]; omega
      have hg0 : (i.val : ℤ) - 1 = (t.val : ℤ) := by omega
      have hg2 : (i.val : ℤ) + 1 = (t.val : ℤ) + 2 := by omega
      have hk : wavenumber k₀ q i.val / q = wavenumber k₀ q t.val := by
        rw [hn, wavenumber_div_ratio k₀ q hq]
      rw [hg0, hg2, ghost_triad_left u t, ghost_triad_right u t, hk]
    · rw [dif_neg h]
      by_cases hi : 1 ≤ i.val
      · have hg : ghost u ((i.val : ℤ) + 1) = 0 := ghost_outside u _ (Or.inr (by omega))
        simp [triadMiddle, hg]
      · have hg : ghost u ((i.val : ℤ) - 1) = 0 := ghost_outside u _ (Or.inl (by omega))
        simp [triadMiddle, hg]
  have hlast :
      (if h : 2 ≤ i.val ∧ i.val - 2 < N then
        triadLast c (wavenumber k₀ q (i.val - 2)) (u (leftShell ⟨i.val - 2, h.2⟩))
          (u (middleShell ⟨i.val - 2, h.2⟩)) else 0) =
      triadLast c (wavenumber k₀ q i.val / (q * q)) (ghost u ((i.val : ℤ) - 2))
        (ghost u ((i.val : ℤ) - 1)) := by
    by_cases h : 2 ≤ i.val ∧ i.val - 2 < N
    · rw [dif_pos h]
      let t : Fin N := ⟨i.val - 2, h.2⟩
      have hn : i.val = t.val + 2 := by dsimp [t]; omega
      have hg0 : (i.val : ℤ) - 2 = (t.val : ℤ) := by omega
      have hg1 : (i.val : ℤ) - 1 = (t.val : ℤ) + 1 := by omega
      have hk : wavenumber k₀ q i.val / (q * q) = wavenumber k₀ q t.val := by
        rw [hn, wavenumber_div_ratio_squared k₀ q hq]
      rw [hg0, hg1, ghost_triad_left u t, ghost_triad_middle u t, hk]
    · rw [dif_neg h]
      have hg : ghost u ((i.val : ℤ) - 2) = 0 := ghost_outside u _ (Or.inl (by omega))
      simp [triadLast, hg]
  rw [hfirst, hmiddle, hlast]

end Research.STPR
