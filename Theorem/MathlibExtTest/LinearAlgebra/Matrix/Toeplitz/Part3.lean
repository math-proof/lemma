/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/


import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Def.LinearAlgebra.Matrix.Toeplitz
import Lemma.Matrix.Toeplitz
import Def.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz.Part2
open MetaMathlibExt


/-- A symmetric Toeplitz matrix is Toeplitz. -/
example : IsToeplitzMatrix symm3 := symm3_isSymmToeplitz.isToeplitz

/-- Symmetry consequence: off-diagonal entries commute. -/
example : symm3 ⟨0, by omega⟩ ⟨2, by omega⟩ =
    symm3 ⟨2, by omega⟩ ⟨0, by omega⟩ :=
  symm3_isSymmToeplitz.entry_comm _ _

