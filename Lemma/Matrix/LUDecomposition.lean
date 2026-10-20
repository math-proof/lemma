import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.LUDecomposition
open MathlibExt.LinearAlgebra.Matrix.LUDecompositionWanted


/--
[exists_lu_decomposition_of_minors_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LUDecomposition.lean)
-/
@[path]
private lemma exists_lu_decomposition_of_minors_ne_zero_eq
  [Field K]
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) K}
-- given
  (h : ∀ (k : ℕ) (hk : k ≤ n), Matrix.det (A.submatrix (Fin.castLE hk) (Fin.castLE hk)) ≠ 0) :
-- imply
  ∃ L U : Matrix (Fin n) (Fin n) K,
    L.IsLowerTriangular ∧ U.IsUpperTriangular ∧ (∀ i, L i i = 1) ∧ A = L * U := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.LUDecompositionWanted.exists_lu_decomposition_of_minors_ne_zero n A h

/--
[lu_decomposition_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LUDecomposition.lean)
-/
@[path]
private lemma lu_decomposition_unique_eq
  [Field K]
  {n : ℕ}
  {A L₁ L₂ U₁ U₂ : Matrix (Fin n) (Fin n) K}
-- given
  (hA : IsUnit A.det)
  (hL₁ : L₁.IsLowerTriangular)
  (hU₁ : U₁.IsUpperTriangular)
  (hd₁ : ∀ i, L₁ i i = 1)
  (hL₂ : L₂.IsLowerTriangular)
  (hU₂ : U₂.IsUpperTriangular)
  (hd₂ : ∀ i, L₂ i i = 1)
  (e₁ : A = L₁ * U₁)
  (e₂ : A = L₂ * U₂) :
-- imply
  L₁ = L₂ ∧ U₁ = U₂ := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.LUDecompositionWanted.lu_decomposition_unique n A L₁ L₂ U₁ U₂ hA hL₁ hU₁ hd₁ hL₂ hU₂ hd₂ e₁ e₂


-- created on 2026-10-20
