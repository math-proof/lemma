module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Def.LinearAlgebra.Matrix.Toeplitz
public import Theorem.Matrix.Toeplitz
public import Theorem.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz.Part2
open MetaMathlibExt


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/
/-- A concrete `3 × 3` symmetric Toeplitz matrix. -/
def symm3 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ :=
  ![![(1 : ℝ), (2 : ℝ), (5 : ℝ)],
    ![(2 : ℝ), (1 : ℝ), (2 : ℝ)],
    ![(5 : ℝ), (2 : ℝ), (1 : ℝ)]]

