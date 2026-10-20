import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.SimultaneousDiagonalization
open MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted


/--
[_root_.Matrix.PosDef.exists_isUnit_transpose_mul_mul_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean)
-/
@[path]
private lemma Matrix_PosDef_exists_isUnit_transpose_mul_mul_eq_one_eq
  [Fintype n] [DecidableEq n]
  {P : Matrix n n ℝ}
-- given
  (hP : P.PosDef) :
-- imply
  ∃ Q : Matrix n n ℝ, IsUnit Q ∧ Matrix.transpose Q * P * Q = 1 := by
-- proof
  apply Matrix.PosDef.exists_isUnit_transpose_mul_mul_eq_one hP

/--
[simultaneous_diagonalization_posDef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean)
-/
@[path]
private lemma simultaneous_diagonalization_posDef_eq
  [Fintype n] [DecidableEq n]
  {S P : Matrix n n ℝ}
-- given
  (hS : S.IsSymm)
  (hP : P.PosDef) :
-- imply
  ∃ C : Matrix n n ℝ,
    IsUnit C ∧ (Matrix.transpose C * S * C).IsDiag ∧ Matrix.transpose C * P * C = 1 := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted.simultaneous_diagonalization_posDef S P hS hP


-- created on 2026-10-20
