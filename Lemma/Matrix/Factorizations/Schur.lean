import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.Factorizations.Schur
open Matrix
open scoped ComplexOrder


/--
[exists_unitaryGroup_isUpperTriangular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Schur.lean)
-/
@[path]
private lemma exists_unitaryGroup_isUpperTriangular_eq
  [Fintype n] [DecidableEq n] [LinearOrder n]
  {A : Matrix n n ℂ} :
-- imply
  ∃ (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ),
    T.IsUpperTriangular ∧ A = (U : Matrix n n ℂ) * T * star (U : Matrix n n ℂ) := by
-- proof
  apply Matrix.exists_unitaryGroup_isUpperTriangular A


-- created on 2026-10-20
