/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/
module

public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Def.LinearAlgebra.Matrix.Toeplitz
public import Theorem.Matrix.Toeplitz
open MetaMathlibExt

public section

/-- Dimension 1: every `1 × 1` real matrix is Toeplitz. -/
example : IsToeplitzMatrix (n := 0) ![![(7 : ℝ)]] :=
  isToeplitzMatrix_of_witness (c := fun _ => (7 : ℝ)) (by
    intro i j
    fin_cases i
    all_goals fin_cases j
    all_goals simp)

