/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/HadamardDeterminant.lean -/

/-
Author: Muse Spark 1.3
-/

import Lemma.Matrix.HadamardDeterminant
import Mathlib.Tactic.NormNum
import Def.MathlibExtTest.LinearAlgebra.Matrix.HadamardDeterminant
open MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant

#check @hadamard_determinant_inequality


example : ‖Adiag.det‖ ≤
    ∏ i : Fin 2, Real.sqrt (∑ j : Fin 2, Complex.normSq (Adiag i j)) :=
  hadamard_determinant_inequality Adiag

/-- The left-hand side evaluates to `6`. -/
example : ‖Adiag.det‖ = 6 := by
  have hdet : Adiag.det = 6 := by
    rw [Adiag, Matrix.det_diagonal]
    norm_num [Fin.prod_univ_two]
  rw [hdet]
  norm_num

/-- The right-hand side evaluates to `2 * 3 = 6` (the bound is tight here). -/
example : (∏ i : Fin 2, Real.sqrt (∑ j : Fin 2, Complex.normSq (Adiag i j))) = 6 := by
  have h0 : (∑ j : Fin 2, Complex.normSq (Adiag 0 j)) = 4 := by
    simp [Adiag, Fin.sum_univ_two, Matrix.diagonal_apply]
    norm_num [Complex.normSq_apply]
  have h1 : (∑ j : Fin 2, Complex.normSq (Adiag 1 j)) = 9 := by
    simp [Adiag, Fin.sum_univ_two, Matrix.diagonal_apply]
    norm_num [Complex.normSq_apply]
  rw [Fin.prod_univ_two, h0, h1]
  have s4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have s9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [s4, s9]
  norm_num

