/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/


import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Def.LinearAlgebra.Matrix.Toeplitz
import Lemma.Matrix.Toeplitz
import Theorem.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz
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

