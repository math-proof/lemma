/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part29
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem doubledBoxResidualMomentEmptyBranchSummand_nonneg
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxResidualMomentEmptyBranchSummand β n v e0 m := by
  dsimp [doubledBoxResidualMomentEmptyBranchSummand]
  refine mul_nonneg hβ ?_
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in

theorem doubledBoxResidualMomentInnerPairBranchSummand_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m := by
  dsimp [doubledBoxResidualMomentInnerPairBranchSummand]
  refine mul_nonneg hβ ?_
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxResidualMomentBranchSummand_eq_empty_add_inner
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxResidualMomentBranchSummand β n v w e0 m =
      doubledBoxResidualMomentEmptyBranchSummand β n v e0 m +
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m := by
  dsimp [doubledBoxResidualMomentBranchSummand,
    doubledBoxResidualMomentEmptyBranchSummand,
    doubledBoxResidualMomentInnerPairBranchSummand]
  ring

set_option linter.style.longLine false in

theorem doubledBoxResidualMomentBranchSummand_finset_sum_eq_empty_add_inner
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω, doubledBoxResidualMomentBranchSummand β n v w e0 m) =
      (∑ m ∈ Ω, doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) +
        (∑ m ∈ Ω,
          doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) := by
  calc
    (∑ m ∈ Ω, doubledBoxResidualMomentBranchSummand β n v w e0 m) =
        ∑ m ∈ Ω,
          (doubledBoxResidualMomentEmptyBranchSummand β n v e0 m +
            doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) := by
      refine Finset.sum_congr rfl ?_
      intro m _hm
      exact doubledBoxResidualMomentBranchSummand_eq_empty_add_inner β n v w e0 m
    _ =
      (∑ m ∈ Ω, doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) +
        (∑ m ∈ Ω,
          doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) := by
      rw [Finset.sum_add_distrib]

set_option linter.style.longLine false in

theorem doubledBoxResidualMomentEmptyBranchSummand_summable
    (β : ℝ) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) := by
  have h :=
    summable_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) e0
  simpa [doubledBoxResidualMomentEmptyBranchSummand] using h.mul_left β

set_option linter.style.longLine false in

theorem doubledBoxResidualMomentInnerPairBranchSummand_summable
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) := by
  have h :=
    summable_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) e0
  simpa [doubledBoxResidualMomentInnerPairBranchSummand] using h.mul_left β

set_option linter.style.longLine false in


theorem doubledBoxResidualMomentBranchSummand_summable_of_branch_summable
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hempty :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m))
    (hinner :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m)) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxResidualMomentBranchSummand β n v w e0 m) := by
  simpa [doubledBoxResidualMomentBranchSummand_eq_empty_add_inner] using
    hempty.add hinner

set_option linter.style.longLine false in

theorem doubledBoxResidualMomentBranchSummand_summable
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxResidualMomentBranchSummand β n v w e0 m) :=
  doubledBoxResidualMomentBranchSummand_summable_of_branch_summable
    (doubledBoxResidualMomentEmptyBranchSummand_summable β n v e0)
    (doubledBoxResidualMomentInnerPairBranchSummand_summable β n v w e0)

set_option linter.style.longLine false in


theorem doubledBoxResidualMomentEmptyBranchSummand_tsum_le_two_beta_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤
      β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  change
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      β * (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) ≤
      β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ hβ
  simpa using
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_two_beta
      (FK.boxGraph 3 (2 * n)) hβ
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) e0

set_option linter.style.longLine false in


theorem doubledBoxResidualMomentInnerPairBranchSummand_tsum_le_two_beta_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) ≤
      β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) := by
  change
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      β * (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m)) ≤
      β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ hβ
  simpa using
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_two_beta
      (FK.boxGraph 3 (2 * n)) hβ
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) e0

set_option linter.style.longLine false in


theorem doubledBoxResidualMomentBranchSummand_tsum_le_two_beta_sourcePairSums
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤
      β * (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) := by
  have hempty :=
    doubledBoxResidualMomentEmptyBranchSummand_tsum_le_two_beta_sourcePairSum
      hβ n v e0
  have hinner :=
    doubledBoxResidualMomentInnerPairBranchSummand_tsum_le_two_beta_sourcePairSum
      hβ n v w e0
  calc
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxResidualMomentBranchSummand β n v w e0 m)
        =
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) +
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) :=
      by
        conv_lhs =>
          congr
          intro m
          rw [doubledBoxResidualMomentBranchSummand_eq_empty_add_inner]
        exact
          Summable.tsum_add
            (doubledBoxResidualMomentEmptyBranchSummand_summable β n v e0)
            (doubledBoxResidualMomentInnerPairBranchSummand_summable β n v w e0)
    _ ≤
      β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
      β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) :=
      add_le_add hempty hinner
    _ =
      β * (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) := by
      ring

set_option linter.style.longLine false in


theorem doubledBoxResidualMomentBranchSummand_tsum_eq_empty_add_inner
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hempty :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m))
    (hinner :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m)) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentBranchSummand β n v w e0 m) =
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) +
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) := by
  conv_lhs =>
    congr
    intro m
    rw [doubledBoxResidualMomentBranchSummand_eq_empty_add_inner]
  exact Summable.tsum_add hempty hinner

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_finite_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hfinite :
      ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
        β *
          ∑ m ∈ Ω,
            (((m e0 + 1 : ℕ) : ℝ) *
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n v)
                (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
              ((m e0 + 1 : ℕ) : ℝ) *
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w) m) ≤
          C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  change
    β *
        edgeCopySourcePairEmptyCollapsedSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v) ≤ C
  rw [edgeCopySourcePairEmptyCollapsedSum_eq_tsum_term]
  rw [← tsum_mul_left]
  refine tsum_le_of_all_finset_sum_le ?_ ?_
  · exact
      (edgeCopySourcePairEmptyCollapsedTerm_summable
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)).mul_left β
  · intro Ω
    change
      (∑ m ∈ Ω,
        β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤ C
    rw [← Finset.mul_sum]
    exact
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_beta_mul_edgeMultiplicitySucc_branchSourcePairSummand_sum
        (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw).trans
        (hfinite Ω)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMomentBranchSummand_finite_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hfinite :
      ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
        (∑ m ∈ Ω, doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  change
    β *
        edgeCopySourcePairEmptyCollapsedSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v) ≤ C
  rw [edgeCopySourcePairEmptyCollapsedSum_eq_tsum_term]
  rw [← tsum_mul_left]
  refine tsum_le_of_all_finset_sum_le ?_ ?_
  · exact
      (edgeCopySourcePairEmptyCollapsedTerm_summable
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)).mul_left β
  · intro Ω
    change
      (∑ m ∈ Ω,
        β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤ C
    rw [← Finset.mul_sum]
    exact
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_residualMomentBranchSummand_sum
        (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw).trans
        (hfinite Ω)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_finite_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hfinite :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            β *
              ∑ m ∈ Ω,
                (((m e0 + 1 : ℕ) : ℝ) *
                  edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n v)
                    (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
                  ((m e0 + 1 : ℕ) : ℝ) *
                  edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n w)
                    (doubledBoxInnerPairSource n v w) m) ≤
              C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_finite_bound
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (hfinite e0 hedge)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMomentBranchSummand_finite_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hfinite :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω, doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤
              C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMomentBranchSummand_finite_bound
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (hfinite e0 hedge)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_tsum_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hsum :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxResidualMomentBranchSummand β n v w e0 m))
    (hbound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_finite_bound
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw ?_
  intro Ω
  calc
    β *
      ∑ m ∈ Ω,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          ((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m)
        =
        ∑ m ∈ Ω, doubledBoxResidualMomentBranchSummand β n v w e0 m := by
          rw [Finset.mul_sum]
          rfl
    _ ≤
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxResidualMomentBranchSummand β n v w e0 m :=
      hsum.sum_le_tsum Ω
        (fun m _hm =>
          doubledBoxResidualMomentBranchSummand_nonneg
            (n := n) (v := v) (w := w) hβ e0 m)
    _ ≤ C := hbound

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_tsum_bound_of_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hbound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_tsum_bound
    (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
    (doubledBoxResidualMomentBranchSummand_summable β n v w e0) hbound

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_two_beta_sourcePairSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      β * (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_tsum_bound_of_bound
    (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
    (doubledBoxResidualMomentBranchSummand_tsum_le_two_beta_sourcePairSums
      hβ n v w e0)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_branch_tsum_bounds
    {β Cempty Cinner C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hempty :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m))
    (hinner :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m))
    (hempty_bound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤ Cempty)
    (hinner_bound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) ≤ Cinner)
    (hbudget : Cempty + Cinner ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_tsum_bound
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw ?_ ?_
  · exact
      doubledBoxResidualMomentBranchSummand_summable_of_branch_summable
        (n := n) (v := v) (w := w) (e0 := e0) hempty hinner
  · calc
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentBranchSummand β n v w e0 m)
          =
        (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) +
        (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) :=
        doubledBoxResidualMomentBranchSummand_tsum_eq_empty_add_inner
          (n := n) (v := v) (w := w) (e0 := e0) hempty hinner
      _ ≤ Cempty + Cinner := add_le_add hempty_bound hinner_bound
      _ ≤ C := hbudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_branch_tsum_bounds_of_bounds
    {β Cempty Cinner C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hempty_bound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤ Cempty)
    (hinner_bound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) ≤ Cinner)
    (hbudget : Cempty + Cinner ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_branch_tsum_bounds
    (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
    (doubledBoxResidualMomentEmptyBranchSummand_summable β n v e0)
    (doubledBoxResidualMomentInnerPairBranchSummand_summable β n v w e0)
    hempty_bound hinner_bound hbudget

end Exact3D
end StatMech
