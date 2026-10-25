/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part3


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem IntervalOffDiagAbsRowSum_nonneg {n : ℕ}
    (I : IntervalMatrix n n) (i : Fin n) :
    0 ≤ IntervalOffDiagAbsRowSum I i := by
  classical
  unfold IntervalOffDiagAbsRowSum
  exact Finset.sum_nonneg fun j _ => by
    by_cases h : j = i
    · simp [h]
    · simp [h, absUpper_nonneg]


theorem IntervalOffDiagAbsRowSum_nonneg_real {n : ℕ}
    (I : IntervalMatrix n n) (i : Fin n) :
    0 ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
  exact_mod_cast IntervalOffDiagAbsRowSum_nonneg I i


theorem matVec_eq_diag_add_offDiag {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    matVec A x i =
      A i i * x i + ∑ j, if j = i then 0 else A i j * x j := by
  classical
  unfold matVec
  calc
    (∑ j, A i j * x j) =
        ∑ j, ((if j = i then A i j * x j else 0) +
          (if j = i then 0 else A i j * x j)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [h]
    _ = (∑ j, if j = i then A i j * x j else 0) +
        ∑ j, if j = i then 0 else A i j * x j := by
      rw [Finset.sum_add_distrib]
    _ = A i i * x i + ∑ j, if j = i then 0 else A i j * x j := by
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro hi
        simp at hi


theorem offDiag_abs_matVec_bound {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    |∑ j, if j = i then 0 else A i j * x j| ≤
      offDiagAbsRowSum A i * |x i| := by
  classical
  calc
    |∑ j, if j = i then 0 else A i j * x j| ≤
        ∑ j, |if j = i then 0 else A i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (if j = i then 0 else |A i j| * |x j|) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [h, abs_mul]
    _ ≤ ∑ j, (if j = i then 0 else |A i j| * |x i|) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j = i
      · simp [h]
      · simpa [h] using
          mul_le_mul_of_nonneg_left (hpivot j) (abs_nonneg (A i j))
    _ = offDiagAbsRowSum A i * |x i| := by
      simp [offDiagAbsRowSum, Finset.sum_mul]


theorem gershgorin_row_bound_of_pivot {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (lam : ℝ) (i : Fin n)
    (heig_i : matVec A x i = lam * x i)
    (hxi : x i ≠ 0)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    |lam - A i i| ≤ offDiagAbsRowSum A i := by
  have hpos : 0 < |x i| := abs_pos.mpr hxi
  have hmul : (lam - A i i) * x i =
      ∑ j, if j = i then 0 else A i j * x j := by
    have hdecomp := matVec_eq_diag_add_offDiag A x i
    rw [heig_i] at hdecomp
    calc
      (lam - A i i) * x i = lam * x i - A i i * x i := by ring
      _ = ∑ j, if j = i then 0 else A i j * x j := by linarith
  have hbound :
      |(lam - A i i) * x i| ≤ offDiagAbsRowSum A i * |x i| := by
    rw [hmul]
    exact offDiag_abs_matVec_bound A x i hpivot
  have hbound' :
      |lam - A i i| * |x i| ≤ offDiagAbsRowSum A i * |x i| := by
    simpa [abs_mul] using hbound
  exact le_of_mul_le_mul_right hbound' hpos


theorem offDiagAbsRowSum_le_interval {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (i : Fin n) :
    offDiagAbsRowSum A i ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
  classical
  calc
    offDiagAbsRowSum A i = ∑ j, if j = i then 0 else |A i j| := rfl
    _ ≤ ∑ j, if j = i then 0 else ((I i j).absUpper : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j = i
      · simp [h]
      · simpa [h] using abs_le_absUpper_of_memR (hA i j)
    _ = (IntervalOffDiagAbsRowSum I i : ℝ) := by
      rw [IntervalOffDiagAbsRowSum, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [h]


theorem gershgorin_interval_row_bound_of_pivot {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ) (i : Fin n)
    (heig_i : matVec A x i = lam * x i)
    (hxi : x i ≠ 0)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    |lam - A i i| ≤ (IntervalOffDiagAbsRowSum I i : ℝ) :=
  le_trans (gershgorin_row_bound_of_pivot A x lam i heig_i hxi hpivot)
    (offDiagAbsRowSum_le_interval hA i)


theorem exists_pivot_of_exists_nonzero {n : ℕ} (x : Fin n → ℝ)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, x i ≠ 0 ∧ ∀ j, |x j| ≤ |x i| := by
  classical
  rcases hnonzero with ⟨i0, hi0⟩
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun i => |x i|) ⟨i0, by simp⟩
  refine ⟨i, ?_, ?_⟩
  · by_contra hxi
    have hxi_zero : x i = 0 := by simpa using hxi
    have hle : |x i0| ≤ 0 := by
      simpa [hxi_zero] using hmax i0 (by simp)
    exact (not_le.mpr (abs_pos.mpr hi0)) hle
  · intro j
    exact hmax j (by simp)


theorem gershgorin_bound_of_eigenvector {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (lam : ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, |lam - A i i| ≤ offDiagAbsRowSum A i := by
  rcases exists_pivot_of_exists_nonzero x hnonzero with ⟨i, hxi, hpivot⟩
  exact ⟨i, gershgorin_row_bound_of_pivot A x lam i (heig i) hxi hpivot⟩


theorem gershgorin_interval_bound_of_eigenvector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, |lam - A i i| ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
  rcases exists_pivot_of_exists_nonzero x hnonzero with ⟨i, hxi, hpivot⟩
  exact ⟨i,
    gershgorin_interval_row_bound_of_pivot hA x lam i (heig i) hxi hpivot⟩


end RatInterval
end Exact3D
end StatMech
