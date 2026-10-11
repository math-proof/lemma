import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.KyFan

open InnerProductSpace.KyFanWanted

/--
[KyFan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/KyFan.lean)
-/
@[path]
private lemma eig_pref_sum_zero_eq
-- given
  {n : ℕ}
  (hk : 0 ≤ n)
  (eig : Fin n → ℝ) :
-- imply
  eigPrefSum eig 0 hk = 0 := by
-- proof
  apply InnerProductSpace.KyFanWanted.eigPrefSum_zero eig hk

/--
[KyFan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/KyFan.lean)
-/
@[path]
private lemma eig_pref_sum_eq_sum_eq
-- given
  {n : ℕ}
  (k : ℕ)
  (hk : k ≤ n)
  (eig : Fin n → ℝ) :
-- imply
  eigPrefSum eig k hk = ∑ i : Fin k, eig (Fin.castLE hk i) := by
-- proof
  apply InnerProductSpace.KyFanWanted.eigPrefSum_eq_sum eig k hk

/--
[KyFan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/KyFan.lean)
-/
@[path]
private lemma eig_pref_sum_succ_eq
-- given
  {n : ℕ}
  (k : ℕ)
  (hk : k + 1 ≤ n)
  (eig : Fin n → ℝ) :
-- imply
  eigPrefSum eig (k + 1) hk = eigPrefSum eig k (Nat.le_of_succ_le hk) + eig ⟨k, hk⟩ := by
-- proof
  apply InnerProductSpace.KyFanWanted.eigPrefSum_succ eig k hk

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
