/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/


import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import sympy.atlas.LinearAlgebra.Matrix.Toeplitz
import Lemma.Matrix.Toeplitz

open MetaMathlibExt

/-- Dimension 1: every `1 × 1` real matrix is Toeplitz. -/
example : IsToeplitzMatrix (n := 0) ![![(7 : ℝ)]] :=
  isToeplitzMatrix_of_witness (c := fun _ => (7 : ℝ)) (by
    intro i j
    fin_cases i
    all_goals fin_cases j
    all_goals simp)

/-- A concrete `3 × 3` Toeplitz matrix. -/
private def toeplitz3 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ :=
  ![![(1 : ℝ), (2 : ℝ), (3 : ℝ)],
    ![(4 : ℝ), (1 : ℝ), (2 : ℝ)],
    ![(5 : ℝ), (4 : ℝ), (1 : ℝ)]]

/-- A concrete `3 × 3` matrix that is not Toeplitz (main diagonal varies). -/
private def nontoep3 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ :=
  ![![(1 : ℝ), (2 : ℝ), (3 : ℝ)],
    ![(4 : ℝ), (5 : ℝ), (6 : ℝ)],
    ![(7 : ℝ), (8 : ℝ), (9 : ℝ)]]

example : ¬ IsToeplitzMatrix nontoep3 := by
  rintro ⟨c, hc⟩
  have h00 := hc ⟨0, by omega⟩ ⟨0, by omega⟩
  have h11 := hc ⟨1, by omega⟩ ⟨1, by omega⟩
  simp [nontoep3] at h00 h11
  have hcontra : (1 : ℝ) = 5 := h00.trans h11.symm
  norm_num at hcontra

/-- A concrete `3 × 3` symmetric Toeplitz matrix. -/
private def symm3 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ :=
  ![![(1 : ℝ), (2 : ℝ), (5 : ℝ)],
    ![(2 : ℝ), (1 : ℝ), (2 : ℝ)],
    ![(5 : ℝ), (2 : ℝ), (1 : ℝ)]]

/-- A symmetric Toeplitz matrix is Toeplitz. -/
example : IsToeplitzMatrix symm3 := symm3_isSymmToeplitz.isToeplitz

/-- Symmetry consequence: off-diagonal entries commute. -/
example : symm3 ⟨0, by omega⟩ ⟨2, by omega⟩ =
    symm3 ⟨2, by omega⟩ ⟨0, by omega⟩ :=
  symm3_isSymmToeplitz.entry_comm _ _
