/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/


import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Def.LinearAlgebra.Matrix.Toeplitz
import Lemma.Matrix.Toeplitz
import Theorem.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz.Part2
open MetaMathlibExt


/-- A concrete `3 × 3` symmetric Toeplitz matrix. -/
def symm3 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ :=
  ![![(1 : ℝ), (2 : ℝ), (5 : ℝ)],
    ![(2 : ℝ), (1 : ℝ), (2 : ℝ)],
    ![(5 : ℝ), (2 : ℝ), (1 : ℝ)]]

