import Research.STPR.FiniteShell

noncomputable section
namespace Research.STPR
open Complex

/-- Exact three-shell specialization, including both physical boundaries. -/
theorem three_shell_nonlinear (b c k : ℝ) (x y z : ℂ) :
    finiteNonlinear (N := 1) b c (fun _ => k) ![x, y, z] =
      ![triadFirst k y z, triadMiddle b k x z, triadLast c k x y] := by
  ext i
  fin_cases i <;>
    simp [finiteNonlinear, assembledNonlinear, triadVector,
      leftShell, middleShell, rightShell, Fin.sum_univ_one]

/-- One inviscid unforced RK4 step in a valid three-shell Sabra model. -/
theorem sabra_rk4_witness_state :
    rk4 (finiteNonlinear (N := 1) (1 / 2) (-1 / 2) (fun _ => 1)) 1 ![1, 0, 1] =
      ![(72959 / 98304 : ℂ), (-7747 / 16384 : ℂ) * I, (217561 / 196608 : ℂ)] := by
  let F := finiteNonlinear (N := 1) (1 / 2) (-1 / 2) (fun _ => 1)
  let a : Fin 3 → ℂ := ![0, -(1 / 2 : ℂ) * I, 0]
  let b : Fin 3 → ℂ := ![-1 / 4, -(1 / 2 : ℂ) * I, 1 / 8]
  let c : Fin 3 → ℂ := ![-17 / 64, -(119 / 256 : ℂ) * I, 7 / 64]
  let d : Fin 3 → ℂ := ![-8449 / 16384, -(3337 / 8192 : ℂ) * I, 5593 / 32768]
  have ha : F ![1, 0, 1] = a := by
    change finiteNonlinear _ _ _ ![1, 0, 1] = a
    rw [three_shell_nonlinear]
    ext i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [a, triadFirst, triadMiddle, triadLast, Complex.mul_re, Complex.mul_im]
  have ya : (![1, 0, 1] : Fin 3 → ℂ) + (1 / 2 : ℝ) • a = ![1, -(1 / 4 : ℂ) * I, 1] := by
    ext i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [a, Pi.smul_apply, Complex.mul_re, Complex.mul_im, Complex.smul_re, Complex.smul_im]
  have hb : F (![1, 0, 1] + (1 / 2 : ℝ) • a) = b := by
    rw [ya]
    change finiteNonlinear _ _ _ ![1, -(1 / 4 : ℂ) * I, 1] = b
    rw [three_shell_nonlinear]
    ext i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [b, triadFirst, triadMiddle, triadLast, Complex.mul_re, Complex.mul_im]
  have yb : (![1, 0, 1] : Fin 3 → ℂ) + (1 / 2 : ℝ) • b = ![7 / 8, -(1 / 4 : ℂ) * I, 17 / 16] := by
    ext i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [b, Pi.smul_apply, Complex.mul_re, Complex.mul_im, Complex.smul_re, Complex.smul_im]
  have hc : F (![1, 0, 1] + (1 / 2 : ℝ) • b) = c := by
    rw [yb]
    change finiteNonlinear _ _ _ ![7 / 8, -(1 / 4 : ℂ) * I, 17 / 16] = c
    rw [three_shell_nonlinear]
    ext i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [c, triadFirst, triadMiddle, triadLast, Complex.mul_re, Complex.mul_im]
  have yc : (![1, 0, 1] : Fin 3 → ℂ) + c = ![47 / 64, -(119 / 256 : ℂ) * I, 71 / 64] := by
    ext i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [c, Complex.mul_re, Complex.mul_im]
  have hd : F (![1, 0, 1] + c) = d := by
    rw [yc]
    change finiteNonlinear _ _ _ ![47 / 64, -(119 / 256 : ℂ) * I, 71 / 64] = d
    rw [three_shell_nonlinear]
    ext i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [d, triadFirst, triadMiddle, triadLast, Complex.mul_re, Complex.mul_im]
  change rk4 F 1 ![1, 0, 1] = _
  simp only [rk4, ha, hb, hc, hd, one_smul]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [a, b, c, d, Pi.smul_apply, Complex.mul_re, Complex.mul_im,
      Complex.smul_re, Complex.smul_im]

/-- RK4 fails exact energy conservation for the actual inviscid Sabra map. -/
theorem sabra_rk4_energy_defect_witness :
    energy (rk4 (finiteNonlinear (N := 1) (1 / 2) (-1 / 2) (fun _ => 1)) 1 ![1, 0, 1]) -
      energy (![1, 0, 1] : Fin 3 → ℂ) = -(42254587 / 77309411328 : ℝ) := by
  rw [sabra_rk4_witness_state]
  norm_num [energy, energyOne, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

end Research.STPR
