/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part3


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem matVec_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    RatInterval.matVec A x i - RatInterval.matVec A y i =
      RatInterval.matVec A (fun j => x j - y j) i := by
  unfold RatInterval.matVec
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring


theorem affineMap_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    RatInterval.affineMap A b x i - RatInterval.affineMap A b y i =
      RatInterval.matVec A (fun j => x j - y j) i := by
  calc
    RatInterval.affineMap A b x i - RatInterval.affineMap A b y i =
        RatInterval.matVec A x i - RatInterval.matVec A y i := by
      unfold RatInterval.affineMap
      ring
    _ = RatInterval.matVec A (fun j => x j - y j) i := matVec_sub A x y i


theorem lipschitz_matVec_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I) :
    LipschitzWithConstant (fun x i => RatInterval.matVec A x i)
      ((n : ℝ) * (hI.c : ℝ)) := by
  intro x y
  unfold l1Dist RatInterval.supNormVec
  calc
    (∑ i, |RatInterval.matVec A x i - RatInterval.matVec A y i|) =
        ∑ i, |RatInterval.matVec A (fun j => x j - y j) i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [matVec_sub]
    _ ≤ ∑ _i : Fin n, (hI.c : ℝ) *
        RatInterval.supNormVec (fun j => x j - y j) := by
      exact Finset.sum_le_sum fun i _ => hI.apply_bound hA _ i
    _ = (n : ℝ) * (hI.c : ℝ) *
        RatInterval.supNormVec (fun j => x j - y j) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring


theorem lipschitz_matVec_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I) :
    LipschitzWithConstant (fun x i => RatInterval.matVec A x i) (hI.c : ℝ) := by
  intro x y
  unfold l1Dist
  calc
    RatInterval.supNormVec
        (fun i => RatInterval.matVec A x i - RatInterval.matVec A y i) =
        RatInterval.supNormVec
          (fun i => RatInterval.matVec A (fun j => x j - y j) i) := by
      congr 1
      funext i
      exact matVec_sub A x y i
    _ ≤ (hI.c : ℝ) * RatInterval.supNormVec (fun j => x j - y j) :=
      hI.apply_l1_bound hA (fun j => x j - y j)


theorem lipschitz_affineMap_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) :
    LipschitzWithConstant (fun x i => RatInterval.affineMap A b x i)
      ((n : ℝ) * (hI.c : ℝ)) := by
  intro x y
  unfold l1Dist RatInterval.supNormVec
  calc
    (∑ i, |RatInterval.affineMap A b x i -
        RatInterval.affineMap A b y i|) =
        ∑ i, |RatInterval.matVec A (fun j => x j - y j) i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [affineMap_sub]
    _ ≤ ∑ _i : Fin n, (hI.c : ℝ) *
        RatInterval.supNormVec (fun j => x j - y j) := by
      exact Finset.sum_le_sum fun i _ => hI.apply_bound hA _ i
    _ = (n : ℝ) * (hI.c : ℝ) *
        RatInterval.supNormVec (fun j => x j - y j) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring


theorem lipschitz_affineMap_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) :
    LipschitzWithConstant (fun x i => RatInterval.affineMap A b x i)
      (hI.c : ℝ) := by
  intro x y
  unfold l1Dist
  calc
    RatInterval.supNormVec
        (fun i => RatInterval.affineMap A b x i -
          RatInterval.affineMap A b y i) =
        RatInterval.supNormVec
          (fun i => RatInterval.matVec A (fun j => x j - y j) i) := by
      congr 1
      funext i
      exact affineMap_sub A b x y i
    _ ≤ (hI.c : ℝ) * RatInterval.supNormVec (fun j => x j - y j) :=
      hI.apply_l1_bound hA (fun j => x j - y j)


theorem lipschitz_affineMatVec_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) :
    LipschitzWithConstant (fun x i => RatInterval.matVec A x i + b i)
      ((n : ℝ) * (hI.c : ℝ)) := by
  simpa [RatInterval.affineMap] using
    lipschitz_affineMap_of_rowSumContraction hI hA b


theorem lipschitz_affineMatVec_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) :
    LipschitzWithConstant (fun x i => RatInterval.matVec A x i + b i)
      (hI.c : ℝ) := by
  simpa [RatInterval.affineMap] using
    lipschitz_affineMap_of_columnSumContraction hI hA b


theorem l1Dist_triangle {n : ℕ} (x y z : Fin n → ℝ) :
    l1Dist x z ≤ l1Dist x y + l1Dist y z := by
  classical
  unfold l1Dist RatInterval.supNormVec
  calc
    (∑ i, |x i - z i|) ≤ ∑ i, (|x i - y i| + |y i - z i|) := by
      apply Finset.sum_le_sum
      intro i _
      have h : x i - z i = (x i - y i) + (y i - z i) := by ring
      rw [h]
      exact abs_add_le _ _
    _ = (∑ i, |x i - y i|) + ∑ i, |y i - z i| := by
      rw [Finset.sum_add_distrib]


theorem l1Dist_self {n : ℕ} (x : Fin n → ℝ) : l1Dist x x = 0 := by
  simp [l1Dist, RatInterval.supNormVec]


theorem l1Dist_eq_zero_iff {n : ℕ} {x y : Fin n → ℝ} :
    l1Dist x y = 0 ↔ x = y :=
  ⟨eq_of_l1Dist_eq_zero, fun h => by cases h; exact l1Dist_self x⟩


theorem l1Dist_comm {n : ℕ} (x y : Fin n → ℝ) :
    l1Dist x y = l1Dist y x := by
  unfold l1Dist RatInterval.supNormVec
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_sub_comm]


end FiniteContraction
end Exact3D
end StatMech
