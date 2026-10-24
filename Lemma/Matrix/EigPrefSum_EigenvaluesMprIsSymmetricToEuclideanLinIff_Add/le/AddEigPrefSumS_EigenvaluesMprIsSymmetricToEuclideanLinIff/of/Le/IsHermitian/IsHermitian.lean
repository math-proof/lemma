import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.KyFan

open InnerProductSpace.KyFanWanted


/--
[KyFan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/KyFan.lean)
-/
@[path]
private lemma ky_fan_eigenvalue_sum_le
-- given
  {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℂ)
  (k : ℕ)
  (hA : A.IsHermitian)
  (hB : B.IsHermitian)
  (hk : k ≤ n) :
-- imply
  eigPrefSum ((Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.add hB)).eigenvalues
      finrank_euclideanSpace_fin) k hk ≤
    eigPrefSum ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
      finrank_euclideanSpace_fin) k hk +
    eigPrefSum ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
      finrank_euclideanSpace_fin) k hk := by
-- proof
  apply InnerProductSpace.KyFanWanted.ky_fan_eigenvalue_sum_le A B hA hB k hk

-- created on 2026-10-10
