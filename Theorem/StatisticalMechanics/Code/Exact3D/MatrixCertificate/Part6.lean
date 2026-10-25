/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem RowSumContraction.apply_bound {n : ℕ} {I : IntervalMatrix n n}
    (hI : RowSumContraction I) {A : Fin n → Fin n → ℝ} (hA : MatrixMem A I)
    (x : Fin n → ℝ) (i : Fin n) :
    |matVec A x i| ≤ (hI.c : ℝ) * supNormVec x := by
  classical
  have hrow : (MatrixAbsRowSum I i : ℝ) ≤ (hI.c : ℝ) := by
    exact_mod_cast hI.row_bound i
  have hsum :
      |matVec A x i| ≤
        (∑ j, |A i j|) * supNormVec x := by
    calc
      |matVec A x i| = |∑ j, A i j * x j| := rfl
      _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j| * |x j| := by
        simp [abs_mul]
      _ ≤ ∑ j, |A i j| * supNormVec x := by
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_coord_le_supNormVec x j) (abs_nonneg _)
      _ = (∑ j, |A i j|) * supNormVec x := by
        rw [Finset.sum_mul]
  have hmatrix : (∑ j, |A i j|) ≤ (MatrixAbsRowSum I i : ℝ) :=
    MatrixMem.row_abs_sum_le hA i
  exact le_trans hsum
    (mul_le_mul_of_nonneg_right (le_trans hmatrix hrow) (supNormVec_nonneg x))


theorem RowSumContraction.constant_lt_one {n : ℕ} {I : IntervalMatrix n n}
    (hI : RowSumContraction I) : (hI.c : ℝ) < 1 := by
  exact_mod_cast hI.c_lt_one


theorem ColumnSumContraction.apply_l1_bound {n : ℕ}
    {I : IntervalMatrix n n} (hI : ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : MatrixMem A I) (x : Fin n → ℝ) :
    supNormVec (fun i => matVec A x i) ≤ (hI.c : ℝ) * supNormVec x := by
  classical
  unfold supNormVec matVec
  calc
    (∑ i, |∑ j, A i j * x j|) ≤
        ∑ i, ∑ j, |A i j * x j| := by
      exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, |A i j| * |x j| := by
      simp [abs_mul]
    _ = ∑ j, ∑ i, |A i j| * |x j| := by
      exact Finset.sum_comm
    _ = ∑ j, (∑ i, |A i j|) * |x j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ ≤ ∑ j, (hI.c : ℝ) * |x j| := by
      apply Finset.sum_le_sum
      intro j _
      have hcol : (∑ i, |A i j|) ≤ (hI.c : ℝ) := by
        exact le_trans (MatrixMem.col_abs_sum_le hA j)
          (by exact_mod_cast hI.col_bound j)
      exact mul_le_mul_of_nonneg_right hcol (abs_nonneg (x j))
    _ = (hI.c : ℝ) * ∑ j, |x j| := by
      rw [Finset.mul_sum]


theorem ColumnSumContraction.constant_lt_one {n : ℕ} {I : IntervalMatrix n n}
    (hI : ColumnSumContraction I) : (hI.c : ℝ) < 1 := by
  exact_mod_cast hI.c_lt_one

end RatInterval
end Exact3D
end StatMech
