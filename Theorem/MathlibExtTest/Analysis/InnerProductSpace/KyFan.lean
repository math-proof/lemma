/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/KyFan.lean -/

/-
Author: @toskua, Avocado
-/

import Theorem.Analysis.InnerProductSpace.KyFan
open MathlibExt.Analysis.InnerProductSpace.KyFanWanted

/-!
# Tests for the Ky Fan eigenvalue inequality
-/


example (eig : Fin 3 → ℝ) : eigPrefSum eig 0 (by norm_num) = 0 := by
  simp

example (eig : Fin 3 → ℝ) : eigPrefSum eig 2 (by norm_num) = eig 0 + eig 1 := by
  rw [eigPrefSum_succ, eigPrefSum_succ, eigPrefSum_zero, zero_add]
  rfl

-- `k = 1`: the largest eigenvalue is subadditive.
example {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hn : 1 ≤ n) :
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.add hB)).eigenvalues
        finrank_euclideanSpace_fin ⟨0, hn⟩ ≤
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin ⟨0, hn⟩ +
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin ⟨0, hn⟩ := by
  simpa [eigPrefSum_succ] using ky_fan_eigenvalue_sum_le A B hA hB 1 hn

