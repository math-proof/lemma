/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificateExample.Part4


namespace StatMech

namespace Exact3D

namespace MatrixCertificateExample

theorem stableColumnClosedBallCertificate_exists_fixedPoint :
    ∃ p : Fin 2 → ℝ,
      (fun x i => RatInterval.matVec stableMatrix x i) p = p ∧
        FiniteContraction.ClosedBall
          stableColumnClosedBallCertificate.center
          stableColumnClosedBallCertificate.radius p :=
  stableColumnClosedBallCertificate.exists_fixedPoint


theorem stableColumnClosedBallCertificate_fixedPoint_eq_zero :
    stableColumnClosedBallCertificate.fixedPoint = 0 :=
  stableColumnClosedBallCertificate.fixedPoint_unique
    stableColumnClosedBallCertificate.fixedPoint_isFixed stableMatrix_map_zero


theorem stableMatrix_apply_bound (x : Fin 2 → ℝ) (i : Fin 2) :
    |RatInterval.matVec stableMatrix x i| ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [stableRowSumContraction] using
    stableRowSumContraction.apply_bound stableMatrix_mem_intervals x i


theorem stablePointMatrix_apply_bound (x : Fin 2 → ℝ) (i : Fin 2) :
    |RatInterval.matVec stableMatrix x i| ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [stablePointMatrixRowSumContraction,
    RatInterval.rowSumContraction_of_pointMatrix] using
    stablePointMatrixRowSumContraction.apply_bound stableMatrix_mem_pointMatrix x i


theorem stableMatrix_apply_l1_bound (x : Fin 2 → ℝ) :
    RatInterval.supNormVec (fun i => RatInterval.matVec stableMatrix x i) ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [stableColumnSumContraction] using
    stableColumnSumContraction.apply_l1_bound stableMatrix_mem_intervals x


theorem stablePointMatrix_apply_l1_bound (x : Fin 2 → ℝ) :
    RatInterval.supNormVec (fun i => RatInterval.matVec stableMatrix x i) ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [stablePointMatrixColumnSumContraction,
    RatInterval.columnSumContraction_of_pointMatrix] using
    stablePointMatrixColumnSumContraction.apply_l1_bound
      stableMatrix_mem_pointMatrix x


theorem stableIntervals_offDiagAbsRowSum_zero (i : Fin 2) :
    RatInterval.IntervalOffDiagAbsRowSum stableIntervals i = 0 := by
  fin_cases i <;>
    norm_num [RatInterval.IntervalOffDiagAbsRowSum, stableIntervals,
      RatInterval.point, RatInterval.absUpper]


theorem stableMatrix_gershgorin_zero_radius
    (x : Fin 2 → ℝ) (lam : ℝ) (i : Fin 2)
    (heig_i : RatInterval.matVec stableMatrix x i = lam * x i)
    (hxi : x i ≠ 0)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    |lam - stableMatrix i i| ≤ 0 := by
  have h := RatInterval.gershgorin_interval_row_bound_of_pivot
    stableMatrix_mem_intervals x lam i heig_i hxi hpivot
  simpa [stableIntervals_offDiagAbsRowSum_zero i] using h


theorem stableMatrix_eigenvalue_gershgorin_zero_radius
    (x : Fin 2 → ℝ) (lam : ℝ)
    (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, |lam - stableMatrix i i| ≤ 0 := by
  rcases RatInterval.gershgorin_interval_bound_of_eigenvector
      stableMatrix_mem_intervals x lam heig hnonzero with ⟨i, hi⟩
  exact ⟨i, by simpa [stableIntervals_offDiagAbsRowSum_zero i] using hi⟩


theorem stableMatrix_eigenvalue_mem_interval_gershgorin_disk
    (x : Fin 2 → ℝ) (lam : ℝ)
    (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, RatInterval.IntervalGershgorinRowDisk stableIntervals lam i :=
  RatInterval.exists_intervalGershgorinRowDisk_of_eigenvector
    stableMatrix_mem_intervals x lam heig hnonzero


theorem stableMatrix_eigenvalue_mem_interval_gershgorin_rowInterval
    (x : Fin 2 → ℝ) (lam : ℝ)
    (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i,
      (RatInterval.IntervalGershgorinRowInterval stableIntervals i).MemR lam :=
  RatInterval.exists_mem_intervalGershgorinRowInterval_of_eigenvector
    stableMatrix_mem_intervals x lam heig hnonzero


theorem stableMatrix_eigenvalue_eq_half_or_third
    (x : Fin 2 → ℝ) (lam : ℝ)
    (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    lam = (1 : ℝ) / 2 ∨ lam = (1 : ℝ) / 3 := by
  rcases stableMatrix_eigenvalue_gershgorin_zero_radius x lam heig hnonzero
    with ⟨i, hi⟩
  have hzero : |lam - stableMatrix i i| = 0 :=
    le_antisymm hi (abs_nonneg _)
  have hdiag : lam = stableMatrix i i :=
    sub_eq_zero.mp (abs_eq_zero.mp hzero)
  fin_cases i
  · left
    norm_num [stableMatrix] at hdiag
    exact hdiag
  · right
    norm_num [stableMatrix] at hdiag
    exact hdiag


theorem stableIntervals_endpointSeparated_zero (i : Fin 2) :
    RatInterval.IntervalGershgorinRowEndpointSeparated stableIntervals 0 i := by
  fin_cases i <;>
    norm_num [RatInterval.IntervalGershgorinRowEndpointSeparated,
      RatInterval.IntervalOffDiagAbsRowSum, stableIntervals,
      RatInterval.point, RatInterval.absUpper]


theorem stableMatrix_not_exists_zero_eigenvector :
    ¬ ∃ x : Fin 2 → ℝ,
      (∀ i, RatInterval.matVec stableMatrix x i = 0 * x i) ∧ ∃ i, x i ≠ 0 :=
  RatInterval.not_exists_eigenvector_of_interval_gershgorin_endpoint_separation
    stableMatrix_mem_intervals 0 stableIntervals_endpointSeparated_zero


theorem stableIntervals_endpointSeparatedOnIcc_near_zero (i : Fin 2) :
    RatInterval.IntervalGershgorinRowEndpointSeparatedOnIcc stableIntervals
      (-(1 : ℝ) / 10) ((1 : ℝ) / 10) i := by
  fin_cases i <;>
    norm_num [RatInterval.IntervalGershgorinRowEndpointSeparatedOnIcc,
      RatInterval.IntervalOffDiagAbsRowSum, stableIntervals,
      RatInterval.point, RatInterval.absUpper]


theorem stableMatrix_not_exists_eigenvector_with_eigenvalue_near_zero :
    ¬ ∃ lam : ℝ, lam ∈ Set.Icc (-(1 : ℝ) / 10) ((1 : ℝ) / 10) ∧
      ∃ x : Fin 2 → ℝ,
        (∀ i, RatInterval.matVec stableMatrix x i = lam * x i) ∧
          ∃ i, x i ≠ 0 :=
  RatInterval.not_exists_eigenvector_in_Icc_of_endpoint_separation
    stableMatrix_mem_intervals
    (-(1 : ℝ) / 10) ((1 : ℝ) / 10)
    stableIntervals_endpointSeparatedOnIcc_near_zero

end MatrixCertificateExample
end Exact3D
end StatMech
