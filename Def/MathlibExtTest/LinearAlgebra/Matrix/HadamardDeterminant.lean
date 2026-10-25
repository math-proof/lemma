/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/HadamardDeterminant.lean -/

/-
Author: Muse Spark 1.3
-/

import Lemma.Matrix.HadamardDeterminant
import Mathlib.Tactic.NormNum
import Theorem.MathlibExtTest.LinearAlgebra.Matrix.HadamardDeterminant
open MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant

#check @hadamard_determinant_inequality


/-- A concrete `2 × 2` diagonal matrix satisfies the bound. -/
def Adiag : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![2, 3]

