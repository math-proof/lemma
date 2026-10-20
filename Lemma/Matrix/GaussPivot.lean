import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.GaussPivot
open MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted


/--
[_root_.Matrix.exists_unitLowerTriangular_mul_submatrix_isRowEchelon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/GaussPivot.lean)
-/
@[path]
private lemma Matrix_exists_unitLowerTriangular_mul_submatrix_isRowEchelon_eq
  [Field K] [Fintype m] [LinearOrder m] [Finite n] [LinearOrder n]
  {A : Matrix m n K} :
-- imply
  ∃ (L : Matrix m m K) (σ : Equiv.Perm m),
    L.IsLowerTriangular ∧ (∀ i, L.diag i = 1) ∧
    (L * A.submatrix σ id).IsRowEchelon := by
-- proof
  apply Matrix.exists_unitLowerTriangular_mul_submatrix_isRowEchelon A

/--
[gauss_pivot_elim_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/GaussPivot.lean)
-/
@[path]
private lemma gauss_pivot_elim_step_eq
  [Field K] [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [DecidableEq n] [LinearOrder n]
  {A : Matrix m n K}
  {r : m}
  {j : n}
  {i₀ : m}
-- given
  (h : A i₀ j ≠ 0) :
-- imply
  ∃ P : Matrix m m K, P.IsLowerTriangular ∧ (∀ i, P.diag i = 1) ∧
    ∀ i > r, (P * A.submatrix (Equiv.swap r i₀) id) i j = 0 := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted.gauss_pivot_elim_step A r j i₀ h

/--
[exists_gauss_elimination_opList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/GaussPivot.lean)
-/
@[path]
private lemma exists_gauss_elimination_opList_eq
  [Field K] [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [DecidableEq n] [LinearOrder n]
  {A : Matrix m n K} :
-- imply
  ∃ (ops : List (Matrix m m K)) (σ : Equiv.Perm m),
    (∀ M ∈ ops, M.IsLowerTriangular ∧ ∀ i, M.diag i = 1) ∧
    (ops.prod * A.submatrix σ id).IsRowEchelon := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted.exists_gauss_elimination_opList A


-- created on 2026-10-20
