/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/


import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Def.LinearAlgebra.Matrix.Toeplitz
import Lemma.Matrix.Toeplitz
open MetaMathlibExt


/-- Dimension 1: every `1 × 1` real matrix is Toeplitz. -/
example : IsToeplitzMatrix (n := 0) ![![(7 : ℝ)]] :=
  isToeplitzMatrix_of_witness (c := fun _ => (7 : ℝ)) (by
    intro i j
    fin_cases i
    all_goals fin_cases j
    all_goals simp)

