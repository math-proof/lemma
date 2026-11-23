/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/

module

public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Def.LinearAlgebra.Matrix.Toeplitz
public import Theorem.Matrix.Toeplitz
public import Theorem.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz

@[expose] public section

open MetaMathlibExt


/-- A concrete `3 × 3` Toeplitz matrix. -/
def toeplitz3 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ :=
  ![![(1 : ℝ), (2 : ℝ), (3 : ℝ)],
    ![(4 : ℝ), (1 : ℝ), (2 : ℝ)],
    ![(5 : ℝ), (4 : ℝ), (1 : ℝ)]]

/-- A concrete `3 × 3` matrix that is not Toeplitz (main diagonal varies). -/
def nontoep3 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ :=
  ![![(1 : ℝ), (2 : ℝ), (3 : ℝ)],
    ![(4 : ℝ), (5 : ℝ), (6 : ℝ)],
    ![(7 : ℝ), (8 : ℝ), (9 : ℝ)]]

