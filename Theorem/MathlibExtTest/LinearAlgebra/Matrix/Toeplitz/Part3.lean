module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Def.LinearAlgebra.Matrix.Toeplitz
public import Theorem.Matrix.Toeplitz
public import Def.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz.Part2
open MetaMathlibExt


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean -/
/-- A symmetric Toeplitz matrix is Toeplitz. -/

example : IsToeplitzMatrix symm3 := symm3_isSymmToeplitz.isToeplitz

/-- Symmetry consequence: off-diagonal entries commute. -/
example : symm3 ⟨0, by omega⟩ ⟨2, by omega⟩ =
    symm3 ⟨2, by omega⟩ ⟨0, by omega⟩ :=
  symm3_isSymmToeplitz.entry_comm _ _

