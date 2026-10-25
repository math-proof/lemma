/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part4


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem mem_intervalGershgorinRowInterval_of_rowDisk {n : ℕ}
    {I : IntervalMatrix n n} {lam : ℝ} {i : Fin n}
    (hdisk : IntervalGershgorinRowDisk I lam i) :
    (IntervalGershgorinRowInterval I i).MemR lam := by
  rcases hdisk with ⟨a, ha, hdist⟩
  rw [abs_le] at hdist
  constructor
  · simpa [IntervalGershgorinRowInterval] using (by
      linarith [ha.1, hdist.1])
  · simpa [IntervalGershgorinRowInterval] using (by
      linarith [ha.2, hdist.2])


theorem intervalGershgorinRowDisk_of_pivot {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ) (i : Fin n)
    (heig_i : matVec A x i = lam * x i)
    (hxi : x i ≠ 0)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    IntervalGershgorinRowDisk I lam i :=
  ⟨A i i, hA i i,
    gershgorin_interval_row_bound_of_pivot hA x lam i heig_i hxi hpivot⟩


theorem exists_intervalGershgorinRowDisk_of_eigenvector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, IntervalGershgorinRowDisk I lam i := by
  rcases exists_pivot_of_exists_nonzero x hnonzero with ⟨i, hxi, hpivot⟩
  exact ⟨i,
    intervalGershgorinRowDisk_of_pivot hA x lam i (heig i) hxi hpivot⟩


theorem exists_mem_intervalGershgorinRowInterval_of_eigenvector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, (IntervalGershgorinRowInterval I i).MemR lam := by
  rcases exists_intervalGershgorinRowDisk_of_eigenvector hA x lam heig hnonzero
    with ⟨i, hdisk⟩
  exact ⟨i, mem_intervalGershgorinRowInterval_of_rowDisk hdisk⟩


end RatInterval
end Exact3D
end StatMech
