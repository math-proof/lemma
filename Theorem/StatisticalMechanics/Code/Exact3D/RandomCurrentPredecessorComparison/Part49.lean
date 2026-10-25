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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part47
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyShiftedWeightGood_zeroProfile
    (β : ℝ) (n : ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSelectedCopyShiftedWeightGood β n e0
      (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) := by
  unfold doubledBoxSelectedCopyShiftedWeightGood
  exact le_of_eq (by
    simpa using
      (weight_ofEdgeFun_singleEdge_homogeneous
        (FK.boxGraph 3 (2 * n)) β e0).symm)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyShiftedWeightBad_selectedEdgeOne_of_beta_lt_two
    {β : ℝ} (hβ : 0 < β) (hβlt : β < 2) (n : ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSelectedCopyShiftedWeightBad β n e0
      (Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0)
        e0 1) := by
  unfold doubledBoxSelectedCopyShiftedWeightBad
  unfold doubledBoxSelectedCopyShiftedWeightGood
  intro hle
  have hweight :
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update
              (Function.update
                (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0)
                e0 1) e0
              ((Function.update
                (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0)
                e0 1) e0 + 1))) =
        β ^ 2 / 2 := by
    simpa [Function.update_self] using
      weight_ofEdgeFun_twoCopies_singleEdge_homogeneous
        (FK.boxGraph 3 (2 * n)) β e0
  have hle' : β ≤ β ^ 2 / 2 := by
    rw [hweight] at hle
    exact hle
  have hlt : β ^ 2 / 2 < β := by
    have hmul : β * β < 2 * β := mul_lt_mul_of_pos_right hβlt hβ
    nlinarith [hmul]
  exact (not_le_of_gt hlt) hle'

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyShiftedWeightBad_selectedEdgeCopies_of_beta_lt_two
    {β : ℝ} (hβ : 0 < β) (hβlt : β < 2) (n : ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) {k : ℕ} (hk : k ≠ 0) :
    doubledBoxSelectedCopyShiftedWeightBad β n e0
      (Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0)
        e0 k) := by
  unfold doubledBoxSelectedCopyShiftedWeightBad
  unfold doubledBoxSelectedCopyShiftedWeightGood
  intro hle
  have hweight :
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update
              (Function.update
                (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0)
                e0 k) e0
              ((Function.update
                (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0)
                e0 k) e0 + 1))) =
        β ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    simpa [Function.update_self] using
      weight_ofEdgeFun_singleEdgeCopies_homogeneous
        (FK.boxGraph 3 (2 * n)) β e0 (k + 1)
  have hle' :
      β ≤ β ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    rw [hweight] at hle
    exact hle
  have hlt :
      β ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) < β :=
    beta_pow_succ_div_factorial_succ_lt_beta_of_beta_lt_two hβ hβlt hk
  exact (not_le_of_gt hlt) hle'

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_weighted_le_selectedCopySplitBound_of_shiftedWeight_ge_beta_on_finset
    {β : ℝ} (hβ : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hweighted :
      (∑ m ∈ Ω,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))) *
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (hlower :
      ∀ m ∈ Ω,
        β ≤
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  let S :=
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
  have hmul :
      β *
          (∑ m ∈ Ω,
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        β * S := by
    calc
      β *
          (∑ m ∈ Ω,
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
          ∑ m ∈ Ω,
            β *
              doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0
                m := by
        rw [Finset.mul_sum]
      _ ≤
          ∑ m ∈ Ω,
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (Function.update m e0 (m e0 + 1))) *
              doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0
                m := by
        refine Finset.sum_le_sum ?_
        intro m hm
        exact
          mul_le_mul_of_nonneg_right (hlower m hm)
            (doubledBoxSelectedCopyTotalPairCardSourcePairSummand_nonneg
              (n := n) (v := v) (w := w) hβ.le e0 m)
      _ ≤ doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w :=
        hweighted
      _ = β * S := by
        rfl
  exact le_of_mul_le_mul_left hmul hβ

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_filter_weighted_budget_filter_not_unweighted_budget
    {β A B : ℝ} (hβ : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop)
    [DecidablePred P]
    (hweightedP :
      (∑ m ∈ Ω.filter P,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))) *
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        β * A)
    (hlowerP :
      ∀ m ∈ Ω.filter P,
        β ≤
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))))
    (hnotP :
      (∑ m ∈ Ω.filter fun m => ¬ P m,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤ B)
    (hbudget :
      A + B ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  let F :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m => doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m
  have hP : (∑ m ∈ Ω.filter P, F m) ≤ A := by
    have hmul :
        β * (∑ m ∈ Ω.filter P, F m) ≤ β * A := by
      calc
        β * (∑ m ∈ Ω.filter P, F m) =
            ∑ m ∈ Ω.filter P, β * F m := by
          rw [Finset.mul_sum]
        _ ≤
            ∑ m ∈ Ω.filter P,
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                    (Function.update m e0 (m e0 + 1))) *
                doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0
                  m := by
          refine Finset.sum_le_sum ?_
          intro m hm
          exact
            mul_le_mul_of_nonneg_right (hlowerP m hm)
              (doubledBoxSelectedCopyTotalPairCardSourcePairSummand_nonneg
                (n := n) (v := v) (w := w) hβ.le e0 m)
        _ ≤ β * A := hweightedP
    exact le_of_mul_le_mul_left hmul hβ
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := Ω) (p := P) (f := F)
  calc
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
        (∑ m ∈ Ω.filter P, F m) +
          ∑ m ∈ Ω.filter fun m => ¬ P m, F m := by
      simpa [F] using hsplit.symm
    _ ≤ A + B := add_le_add hP hnotP
    _ ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) :=
      hbudget

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_good_weighted_budget_bad_unweighted_budget
    {β A B : ℝ} (hβ : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    [DecidablePred (doubledBoxSelectedCopyShiftedWeightGood β n e0)]
    [DecidablePred (doubledBoxSelectedCopyShiftedWeightBad β n e0)]
    (hweightedGood :
      (∑ m ∈ Ω.filter (doubledBoxSelectedCopyShiftedWeightGood β n e0),
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))) *
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        β * A)
    (hbad :
      (∑ m ∈ Ω.filter (doubledBoxSelectedCopyShiftedWeightBad β n e0),
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤ B)
    (hbudget :
      A + B ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  classical
  refine
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_filter_weighted_budget_filter_not_unweighted_budget
      (n := n) (v := v) (w := w) hβ Ω e0
      (doubledBoxSelectedCopyShiftedWeightGood β n e0) hweightedGood ?_ ?_
      hbudget
  · intro m hm
    exact (Finset.mem_filter.mp hm).2
  · simpa [doubledBoxSelectedCopyShiftedWeightBad] using hbad

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_weightedBound_of_good_on_finset
    {β : ℝ} (hβ : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hweighted :
      doubledBoxWeightedSelectedCopyTotalPairCardSourcePairBound β n v w e0)
    (hgood :
      ∀ m ∈ Ω, doubledBoxSelectedCopyShiftedWeightGood β n e0 m) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_weighted_le_selectedCopySplitBound_of_shiftedWeight_ge_beta_on_finset
      (n := n) (v := v) (w := w) hβ Ω e0 (hweighted Ω)
      (by
        intro m hm
        simpa [doubledBoxSelectedCopyShiftedWeightGood] using hgood m hm)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_bad_filter_sum_eq_zero_of_forall_bad_zero
    {β : ℝ} (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    [DecidablePred (doubledBoxSelectedCopyShiftedWeightBad β n e0)]
    (hzero :
      ∀ m, m ∈ Ω →
        doubledBoxSelectedCopyShiftedWeightBad β n e0 m →
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m = 0) :
    (∑ m ∈ Ω.filter (doubledBoxSelectedCopyShiftedWeightBad β n e0),
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact hzero m (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hm).2

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_weightedBound_of_bad_sum_nonpos
    {β : ℝ} (hβ : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    [DecidablePred (doubledBoxSelectedCopyShiftedWeightBad β n e0)]
    (hweighted :
      doubledBoxWeightedSelectedCopyTotalPairCardSourcePairBound β n v w e0)
    (hbadNonpos :
      (∑ m ∈ Ω.filter (doubledBoxSelectedCopyShiftedWeightBad β n e0),
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤ 0) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  classical
  let S :=
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
  refine
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_good_weighted_budget_bad_unweighted_budget
      (A := S) (B := 0) (n := n) (v := v) (w := w) hβ Ω e0 ?_ ?_ ?_
  · simpa [S, doubledBoxOriginToInnerEndpointSelectedCopySplitBound]
      using hweighted (Ω.filter (doubledBoxSelectedCopyShiftedWeightGood β n e0))
  · exact hbadNonpos
  · simp [S]

set_option linter.style.longLine false in


theorem doubledBoxUnweightedSelectedCopyTotalPairCardSourcePairBound_of_weighted_of_shiftedWeight_ge_beta
    {β : ℝ} (hβ : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hweighted :
      doubledBoxWeightedSelectedCopyTotalPairCardSourcePairBound β n v w e0)
    (hlower :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        β ≤
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1)))) :
    doubledBoxUnweightedSelectedCopyTotalPairCardSourcePairBound β n v w e0 := by
  intro Ω
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_weighted_le_selectedCopySplitBound_of_shiftedWeight_ge_beta_on_finset
      (n := n) (v := v) (w := w) hβ Ω e0 (hweighted Ω)
      (fun m _hm => hlower m)

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_summable
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) := by
  let S :=
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    refine add_nonneg ?_ ?_
    · simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum,
        sourcePairSum_eq_edgeCopySourcePairSum] using
        edgeCopySourcePairSum_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) hβ
          (by intro e; norm_num)
    · simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
        edgeCopySourcePairSum_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) hβ
          (by intro e; norm_num)
  have hdom :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        S * (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m)) :=
    Summable.mul_left S
      (beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_summable
        β n w e0)
  refine Summable.of_nonneg_of_le ?hnonneg ?hle hdom
  · intro m
    have hfactor :
        0 ≤ β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m :=
      mul_nonneg hβ
        (doubledBoxAllComplementWitnessCardWeightFactor_nonneg hβ e0 m)
    have hbranch :
        0 ≤
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m := by
      refine add_nonneg ?_ ?_
      · exact
          edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
            (by intro e; norm_num)
      · exact
          edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m hβ
            (by intro e; norm_num)
    rw [
      weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_beta_mul_allComplementWitnessCardWeightFactor]
    exact mul_nonneg hfactor hbranch
  · intro m
    have hfactor :
        0 ≤ β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m :=
      mul_nonneg hβ
        (doubledBoxAllComplementWitnessCardWeightFactor_nonneg hβ e0 m)
    rw [
      weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_beta_mul_allComplementWitnessCardWeightFactor]
    calc
      (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) *
          (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) ≤
          (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) *
            S := by
        exact
          mul_le_mul_of_nonneg_left
            (doubledBoxSelectedCopyBranchSourcePairSummand_add_le_sourcePairSplitSum
              hβ n v w m) hfactor
      _ =
          S * (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) := by
        ring

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_tsum_le_allComplementTwoBeta_mul_sourcePairSplitSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      (∑ B : Finset (FK.boxVerts 3 (2 * n)),
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B) *
        (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) := by
  refine tsum_le_of_all_finset_sum_le ?_ ?_
  · exact
      weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_summable
        (n := n) (v := v) (w := w) hβ e0
  · intro Ω
    exact
      weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_allComplementTwoBeta_mul_sourcePairSplitSum
        (n := n) (v := v) (w := w) hβ Ω e0

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_tsum_le_selectedCopySplitBound_of_allComplementTwoBeta_le_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hall :
      (∑ B : Finset (FK.boxVerts 3 (2 * n)),
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B) ≤ β) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  let S :=
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
  let T :=
    ∑ B : Finset (FK.boxVerts 3 (2 * n)),
      edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using
      doubledBoxOriginToInnerEndpointSourcePairSplitSum_nonneg hβ n v w
  have hprod :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))) *
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        T * S := by
    simpa [T, S] using
      weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_tsum_le_allComplementTwoBeta_mul_sourcePairSplitSum
        (n := n) (v := v) (w := w) hβ e0
  calc
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m)
        ≤ T * S := hprod
    _ ≤ β * S := by
      exact mul_le_mul_of_nonneg_right (by simpa [T] using hall) hS_nonneg
    _ = doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
      rfl

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_tsum_le_selectedCopySplitBound_of_allComplementTwoBetaMassCap
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hcap : doubledBoxAllComplementTwoBetaMassCap β n w) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w :=
  weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_tsum_le_selectedCopySplitBound_of_allComplementTwoBeta_le_beta
    (n := n) (v := v) (w := w) hβ e0
    (by simpa [doubledBoxAllComplementTwoBetaMassCap] using hcap)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourceSectorCap_mul_residualMomentBranchSummand_sum
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hcap :
      ∀ m ∈ Ω,
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) ≤ C) :
    β * (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      C * ∑ m ∈ Ω,
        doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  calc
    β * (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
        ∑ m ∈ Ω,
          (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w)
              (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
            doubledBoxResidualMomentBranchSummand β n v w e0 m := by
      exact
        beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_sourceSector_card_mul_residualMomentBranchSummand
          β n v w Ω e0
    _ ≤ ∑ m ∈ Ω,
          C * doubledBoxResidualMomentBranchSummand β n v w e0 m := by
      refine Finset.sum_le_sum ?_
      intro m hm
      exact
        mul_le_mul_of_nonneg_right (hcap m hm)
          (doubledBoxResidualMomentBranchSummand_nonneg
            (n := n) (v := v) (w := w) hβ e0 m)
    _ = C * ∑ m ∈ Ω,
          doubledBoxResidualMomentBranchSummand β n v w e0 m := by
      rw [Finset.mul_sum]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_of_sourceSectorCap_residualMomentBranchSummand_sum_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hcap :
      ∀ m ∈ Ω,
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) ≤ C)
    (hbudget :
      C * (∑ m ∈ Ω,
        doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w))) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
  have hmul :
      β * (∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) :=
    (beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourceSectorCap_mul_residualMomentBranchSummand_sum
      (n := n) (v := v) (w := w) hβ.le Ω e0 hcap).trans hbudget
  exact le_of_mul_le_mul_left hmul hβ

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_summable_of_sourceSectorCap
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hcap :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) ≤ C) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) := by
  have hdom :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        (β⁻¹ * C) *
          doubledBoxResidualMomentBranchSummand β n v w e0 m) :=
    (doubledBoxResidualMomentBranchSummand_summable β n v w e0).mul_left
      (β⁻¹ * C)
  refine Summable.of_nonneg_of_le ?hnonneg ?hle hdom
  · intro m
    exact
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand_nonneg
        (n := n) (v := v) (w := w) hβ.le e0 m
  · intro m
    have hres_nonneg :
        0 ≤ doubledBoxResidualMomentBranchSummand β n v w e0 m :=
      doubledBoxResidualMomentBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ.le e0 m
    calc
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
          β⁻¹ *
            (β *
              doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w
                e0 m) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]
      _ =
          β⁻¹ *
            ((((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n w)
                (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
              doubledBoxResidualMomentBranchSummand β n v w e0 m) := by
        rw [
          beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSector_card_mul_residualMomentBranchSummand]
      _ ≤
          β⁻¹ *
            (C * doubledBoxResidualMomentBranchSummand β n v w e0 m) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hcap m) hres_nonneg)
            (inv_nonneg.mpr hβ.le)
      _ =
          (β⁻¹ * C) *
            doubledBoxResidualMomentBranchSummand β n v w e0 m := by
        ring

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_summable_of_sourceSectorResidualMomentBranchSummand_summable
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hsum :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m)) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) := by
  have hscaled :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        β⁻¹ * doubledBoxSourceSectorResidualMomentBranchSummand β n v w
          e0 m) :=
    hsum.mul_left β⁻¹
  refine hscaled.congr ?_
  intro m
  calc
    β⁻¹ * doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m =
        β⁻¹ *
          (β * doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w
            e0 m) := by
      rw [
        doubledBoxSourceSectorResidualMomentBranchSummand_eq_beta_mul_totalPairCardSourcePairSummand]
    _ = doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_summable_of_sourceSectorResidualMomentEmptyBranchSummand_summable
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hsum :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0
          m)) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
        m) := by
  have hscaled :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        β⁻¹ *
          doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0
            m) :=
    hsum.mul_left β⁻¹
  refine hscaled.congr ?_
  intro m
  calc
    β⁻¹ * doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m =
        β⁻¹ *
          (β *
            doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
              e0 m) := by
      rw [
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_totalPairCardEmptySourcePairSummand]
    _ =
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
          m := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_summable_of_sourceSectorResidualMomentInnerPairBranchSummand_summable
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hsum :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m)) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
        e0 m) := by
  have hscaled :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        β⁻¹ *
          doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
            e0 m) :=
    hsum.mul_left β⁻¹
  refine hscaled.congr ?_
  intro m
  calc
    β⁻¹ * doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m =
        β⁻¹ *
          (β *
            doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
              v w e0 m) := by
      rw [
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_totalPairCardInnerPairSourcePairSummand]
    _ =
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
          e0 m := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_tsum_le_of_sourceSectorResidualMomentEmptyBranchSummand_tsum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0
          m) ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
        m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  have hmul :
      β * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
          m) ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
    calc
      β * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
          m) =
          ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            β *
              doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v
                w e0 m := by
        rw [← tsum_mul_left]
      _ =
          ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w
              e0 m := by
        refine tsum_congr ?_
        intro m
        exact
          beta_mul_doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSectorResidualMomentEmptyBranchSummand
            β n v w e0 m
      _ ≤ β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v :=
        hbound
  exact le_of_mul_le_mul_left hmul hβ

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_tsum_le_of_sourceSectorResidualMomentInnerPairBranchSummand_tsum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m) ≤
        β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
        e0 m) ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  have hmul :
      β * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
          e0 m) ≤
        β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
    calc
      β * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
          e0 m) =
          ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            β *
              doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β
                n v w e0 m := by
        rw [← tsum_mul_left]
      _ =
          ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
              e0 m := by
        refine tsum_congr ?_
        intro m
        exact
          beta_mul_doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSectorResidualMomentInnerPairBranchSummand
            β n v w e0 m
      _ ≤
          β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) :=
        hbound
  exact le_of_mul_le_mul_left hmul hβ

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_tsum_le_of_sourceSectorResidualMomentBranchSummand_tsum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w))) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
  have hmul :
      β * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) := by
    calc
      β * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
          ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            β * doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w
              e0 m := by
        rw [← tsum_mul_left]
      _ =
          ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m := by
        refine tsum_congr ?_
        intro m
        exact
          beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSectorResidualMomentBranchSummand
            β n v w e0 m
      _ ≤
          β *
            (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
              Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w)) :=
        hbound
  exact le_of_mul_le_mul_left hmul hβ

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentBranchSummand_summable_of_branch_summable
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hempty :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m))
    (hinner :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m)) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m) := by
  simpa [doubledBoxSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
    using hempty.add hinner

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentBranchSummand_tsum_eq_empty_add_inner
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hempty :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m))
    (hinner :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m)) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m) =
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m) +
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m) := by
  conv_lhs =>
    congr
    intro m
    rw [doubledBoxSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
  exact Summable.tsum_add hempty hinner

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentBranchSummand_tsum_le_of_branch_tsum_bound
    {β T : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hempty :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m))
    (hinner :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m))
    (hbound :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m) +
        (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
            e0 m) ≤ T) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m) ≤ T := by
  rw [doubledBoxSourceSectorResidualMomentBranchSummand_tsum_eq_empty_add_inner
    hempty hinner]
  exact hbound

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_eq_branchCardSourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1)) =
      doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m := by
  rw [
    doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_eq_branchCard_mul_sourcePairSummands]
  rfl

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_finset_sum_eq_branchCardSourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1))) =
      ∑ m ∈ Ω,
        doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m := by
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_eq_branchCardSourcePairSummand
      (β := β) (n := n) (v := v) (w := w) m e0

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyBranchCardSourcePairSummand_le_selectedPairCard_mul_sourcePairSummand_add
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m ≤
      (((edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
         edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m)) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  let Sin := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0
  let Sout := edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0
  let Sall := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  let X :=
    edgeCopySourcePairSummand G β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  let Y :=
    edgeCopySourcePairSummand G β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hSin_subset : Sin ⊆ Sall := by
    intro p hp
    have hp' :
        p ∈ (edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0).filter
          (fun p => p.2 ∈ p.1) := by
      simpa [Sin, edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent] using hp
    exact (Finset.mem_filter.mp hp').1
  have hSout_subset : Sout ⊆ Sall := by
    intro p hp
    have hp' :
        p ∈ (edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0).filter
          (fun p => p.2 ∉ p.1) := by
      simpa [Sout, edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent]
        using hp
    exact (Finset.mem_filter.mp hp').1
  have hSin_card :
      (Sin.card : ℝ) ≤ (Sall.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSin_subset
  have hSout_card :
      (Sout.card : ℝ) ≤ (Sall.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSout_subset
  have hX : 0 ≤ X := by
    dsimp [X, G]
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  have hY : 0 ≤ Y := by
    dsimp [Y, G]
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  change
    (Sin.card : ℝ) * X + (Sout.card : ℝ) * Y ≤
      (Sall.card : ℝ) * (X + Y)
  calc
    (Sin.card : ℝ) * X + (Sout.card : ℝ) * Y ≤
        (Sall.card : ℝ) * X + (Sall.card : ℝ) * Y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hSin_card hX)
        (mul_le_mul_of_nonneg_right hSout_card hY)
    _ = (Sall.card : ℝ) * (X + Y) := by ring

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_le_selectedPairCard_mul_sourcePairSummand_add
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1)) ≤
      (((edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
         edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m)) := by
  rw [
    doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_eq_branchCardSourcePairSummand]
  exact
    doubledBoxSelectedCopyBranchCardSourcePairSummand_le_selectedPairCard_mul_sourcePairSummand_add
      (n := n) (v := v) (w := w) hβ m e0

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyBranchCardSourcePairSummand_finset_sum_le_selectedPairCard_mul_sourcePairSummand_add
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) ≤
      ∑ m ∈ Ω,
        (((edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m e0 (m e0 + 1)) e0).card : ℝ) *
          (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
           edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m)) := by
  refine Finset.sum_le_sum ?_
  intro m _hm
  exact
    doubledBoxSelectedCopyBranchCardSourcePairSummand_le_selectedPairCard_mul_sourcePairSummand_add
      (n := n) (v := v) (w := w) hβ m e0

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_finset_sum_le_selectedPairCard_mul_sourcePairSummand_add
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1))) ≤
      ∑ m ∈ Ω,
        (((edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m e0 (m e0 + 1)) e0).card : ℝ) *
          (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
           edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m)) := by
  refine Finset.sum_le_sum ?_
  intro m _hm
  exact
    doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_le_selectedPairCard_mul_sourcePairSummand_add
      (n := n) (v := v) (w := w) hβ m e0

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyBranchCardSourcePairSummand_le_totalPairCardSourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m ≤
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m := by
  simpa [doubledBoxSelectedCopyTotalPairCardSourcePairSummand] using
    doubledBoxSelectedCopyBranchCardSourcePairSummand_le_selectedPairCard_mul_sourcePairSummand_add
      (n := n) (v := v) (w := w) hβ m e0

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_le_totalPairCardSourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1)) ≤
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m := by
  rw [
    doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_eq_branchCardSourcePairSummand]
  exact
    doubledBoxSelectedCopyBranchCardSourcePairSummand_le_totalPairCardSourcePairSummand
      (n := n) (v := v) (w := w) hβ m e0

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyBranchCardSourcePairSummand_finset_sum_le_totalPairCardSourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m := by
  refine Finset.sum_le_sum ?_
  intro m _hm
  exact
    doubledBoxSelectedCopyBranchCardSourcePairSummand_le_totalPairCardSourcePairSummand
      (n := n) (v := v) (w := w) hβ m e0

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_finset_sum_le_totalPairCardSourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1))) ≤
      ∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m := by
  refine Finset.sum_le_sum ?_
  intro m _hm
  exact
    doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_le_totalPairCardSourcePairSummand
      (n := n) (v := v) (w := w) hβ m e0

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_decrementImageBranchSum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
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
    (habsorb :
      (∑ m ∈ Ω,
        doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
          (Function.update m e0 (m e0 + 1))) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  classical
  let φ : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
    fun m => Function.update m e0 (m e0 + 1)
  calc
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') =
        ∑ m ∈ Ω,
          ((φ m e0 : ℕ) : ℝ) *
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w (φ m) := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact edgeMultiplicityIncrement_injective e0 hxy
    _ ≤ ∑ m ∈ Ω,
          β * doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
            (φ m) := by
      refine Finset.sum_le_sum ?_
      intro m _hm
      exact
        doubledBox_edge_count_mul_targetTerm_le_beta_mul_selectedEdgeCopyBranchSourcePairSummandImageSums
          (n := n) (v := v) (w := w) hβ (φ m) e0 hedge hov how hvw
    _ = β *
        (∑ m ∈ Ω,
          doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
            (φ m)) := by
      rw [← Finset.mul_sum]
    _ ≤ β *
        (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) := by
      exact mul_le_mul_of_nonneg_left habsorb hβ
    _ = doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
      rfl

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_branchCardSourcePairSummand_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
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
    (habsorb :
      (∑ m ∈ Ω,
        doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_decrementImageBranchSum_bound
      (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw ?_
  calc
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1))) =
        ∑ m ∈ Ω,
          doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m := by
      exact
        doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_finset_sum_eq_branchCardSourcePairSummand
          (β := β) (n := n) (v := v) (w := w) Ω e0
    _ ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) :=
      habsorb

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_filter_fullSource_branchCardSourcePairSummand_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
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
    (habsorb :
      (∑ m ∈ Ω.filter
        (fun m =>
          Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
                (Function.update m e0 (m e0 + 1)))
              (Finset.univ :
                Finset (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n))
                  (Function.update m e0 (m e0 + 1)))) =
            doubledBoxOriginToInnerEndpointSource n w),
        doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  classical
  let φ : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
    fun m => Function.update m e0 (m e0 + 1)
  let P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    fun m =>
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) (φ m))
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (φ m))) =
        doubledBoxOriginToInnerEndpointSource n w
  let F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      ((φ m e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w (φ m)
  have hzero : ∀ m ∈ Ω, m ∉ Ω.filter P → F m = 0 := by
    intro m hm hnotActive
    have hnotP : ¬ P m := by
      intro hPm
      exact hnotActive (Finset.mem_filter.mpr ⟨hm, hPm⟩)
    have hterm :
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w (φ m) = 0 := by
      exact
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_eq_zero_of_not_fullSource
          (β := β) (n := n) (v := w) (m := φ m) hnotP
    simp [F, hterm]
  have hsum_filter : (∑ m ∈ Ω.filter P, F m) = ∑ m ∈ Ω, F m := by
    exact Finset.sum_subset (Finset.filter_subset P Ω) hzero
  have hfiltered :
      (∑ m' ∈ (Ω.filter P).image
          (fun m => Function.update m e0 (m e0 + 1)),
        ((m' e0 : ℕ) : ℝ) *
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
    refine
      doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_branchCardSourcePairSummand_bound
        (n := n) (v := v) (w := w) (Ω.filter P) e0 hβ hedge hov how hvw ?_
    simpa [P, φ] using habsorb
  calc
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') =
        ∑ m ∈ Ω, F m := by
      dsimp [F, φ]
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact edgeMultiplicityIncrement_injective e0 hxy
    _ = ∑ m ∈ Ω.filter P, F m := hsum_filter.symm
    _ =
        ∑ m' ∈ (Ω.filter P).image
            (fun m => Function.update m e0 (m e0 + 1)),
          ((m' e0 : ℕ) : ℝ) *
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' := by
      dsimp [F, φ]
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact edgeMultiplicityIncrement_injective e0 hxy
    _ ≤ doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w :=
      hfiltered

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_filter_switchedSourceSectorResidualMomentBranchSummand_sum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 < β)
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
    (hbudget :
      (∑ m ∈ Ω.filter
        (fun m =>
          Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
                (Function.update m e0 (m e0 + 1)))
              (Finset.univ :
                Finset (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n))
                  (Function.update m e0 (m e0 + 1)))) =
            doubledBoxOriginToInnerEndpointSource n w),
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
          doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w))) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  classical
  let φ : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
    fun m => Function.update m e0 (m e0 + 1)
  let P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    fun m =>
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) (φ m))
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (φ m))) =
        doubledBoxOriginToInnerEndpointSource n w
  have hfull :
      ∀ m ∈ Ω.filter P,
        Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))
            (Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n))
                (Function.update m e0 (m e0 + 1)))) =
          doubledBoxOriginToInnerEndpointSource n w := by
    intro m hm
    simpa [P, φ] using (Finset.mem_filter.mp hm).2
  have hswitched :
      β * (∑ m ∈ Ω.filter P,
        doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) ≤
        ∑ m ∈ Ω.filter P,
          (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
            doubledBoxResidualMomentBranchSummand β n v w e0 m := by
    exact
      beta_mul_doubledBoxSelectedCopyBranchCardSourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentBranchSummand_sum
        (n := n) (v := v) (w := w) hβ.le (Ω.filter P) e0 hfull
        hedge hov how hvw
  have hbudgetP :
      (∑ m ∈ Ω.filter P,
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
          doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) := by
    simpa [P, φ] using hbudget
  have habsorbP :
      (∑ m ∈ Ω.filter P,
        doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
    (doubledBoxInnerPairSource n v w) := by
    have hle :=
      hswitched.trans hbudgetP
    exact le_of_mul_le_mul_left hle hβ
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_filter_fullSource_branchCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) Ω e0 hβ.le hedge hov how hvw ?_
  simpa [P, φ] using habsorbP

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_totalPairCardSourcePairSummand_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
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
    (habsorb :
      (∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_branchCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw ?_
  exact
    (doubledBoxSelectedCopyBranchCardSourcePairSummand_finset_sum_le_totalPairCardSourcePairSummand
      (n := n) (v := v) (w := w) hβ Ω e0).trans habsorb

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_unweightedSelectedCopyTotalPairCardSourcePairBound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
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
      doubledBoxUnweightedSelectedCopyTotalPairCardSourcePairBound β n v w e0) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w :=
  doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_totalPairCardSourcePairSummand_bound
    (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw (hbound Ω)

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_weightedSelectedCopyTotalPairCardSourcePairBound_of_shiftedWeight_ge_beta_on_finset
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 < β)
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
    (hweighted :
      doubledBoxWeightedSelectedCopyTotalPairCardSourcePairBound β n v w e0)
    (hlower :
      ∀ m ∈ Ω,
        β ≤
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_totalPairCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) Ω e0 hβ.le hedge hov how hvw ?_
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_weighted_le_selectedCopySplitBound_of_shiftedWeight_ge_beta_on_finset
      (n := n) (v := v) (w := w) hβ Ω e0 (hweighted Ω) hlower

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_allComplementTwoBetaMassCap_of_shiftedWeight_ge_beta_on_finset
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 < β)
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
    (hcap : doubledBoxAllComplementTwoBetaMassCap β n w)
    (hlower :
      ∀ m ∈ Ω,
        β ≤
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  exact
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_weightedSelectedCopyTotalPairCardSourcePairBound_of_shiftedWeight_ge_beta_on_finset
      (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw
      (doubledBoxWeightedSelectedCopyTotalPairCardSourcePairBound_of_allComplementTwoBetaMassCap
        (n := n) (v := v) (w := w) hβ.le e0 hcap)
      hlower

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_filter_weighted_budget_filter_not_unweighted_budget
    {β A B : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop)
    [DecidablePred P]
    (hβ : 0 < β)
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
    (hweightedP :
      (∑ m ∈ Ω.filter P,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))) *
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        β * A)
    (hlowerP :
      ∀ m ∈ Ω.filter P,
        β ≤
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))))
    (hnotP :
      (∑ m ∈ Ω.filter fun m => ¬ P m,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤ B)
    (hbudget :
      A + B ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_totalPairCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) Ω e0 hβ.le hedge hov how hvw ?_
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_filter_weighted_budget_filter_not_unweighted_budget
      (n := n) (v := v) (w := w) hβ Ω e0 P hweightedP hlowerP
      hnotP hbudget

set_option linter.style.longLine false in

theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_good_weighted_budget_bad_unweighted_budget
    {β A B : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    [DecidablePred (doubledBoxSelectedCopyShiftedWeightGood β n e0)]
    [DecidablePred (doubledBoxSelectedCopyShiftedWeightBad β n e0)]
    (hβ : 0 < β)
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
    (hweightedGood :
      (∑ m ∈ Ω.filter (doubledBoxSelectedCopyShiftedWeightGood β n e0),
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))) *
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        β * A)
    (hbad :
      (∑ m ∈ Ω.filter (doubledBoxSelectedCopyShiftedWeightBad β n e0),
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤ B)
    (hbudget :
      A + B ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_totalPairCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) Ω e0 hβ.le hedge hov how hvw ?_
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_sourcePairSplitSum_of_good_weighted_budget_bad_unweighted_budget
      (n := n) (v := v) (w := w) hβ Ω e0 hweightedGood hbad hbudget

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_singleton_zeroProfile_le_selectedCopySplitBound_of_allComplementTwoBetaMassCap
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 < β)
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
    (hcap : doubledBoxAllComplementTwoBetaMassCap β n w) :
    (∑ m' ∈
        ({fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)).image
          (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_allComplementTwoBetaMassCap_of_shiftedWeight_ge_beta_on_finset
      (n := n) (v := v) (w := w)
      ({fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0} :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
      e0 hβ hedge hov how hvw hcap ?_
  intro m hm
  have hmzero :
      m = fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0 := by
    simpa using hm
  subst m
  exact le_of_eq (by
    simpa using
      (weight_ofEdgeFun_singleEdge_homogeneous
        (FK.boxGraph 3 (2 * n)) β e0).symm)

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_singleton_selectedEdgeCopies_le_selectedCopySplitBound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) (k : ℕ)
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
    (∑ m' ∈ (doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k).image
        (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_totalPairCardSourcePairSummand_bound
      (n := n) (v := v) (w := w)
      (doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k)
      e0 hβ hedge hov how hvw ?_
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_singleton_selectedEdgeCopies_sum_le_sourcePairSplitSum
      (n := n) (v := v) (w := w) hβ e0 k hedge hov how

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_sourceSectorCap_residualMomentBranchSummand_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 < β)
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
    (hcap :
      ∀ m ∈ Ω,
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) ≤ C)
    (hbudget :
      C * (∑ m ∈ Ω,
        doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w))) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_totalPairCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) Ω e0 hβ.le hedge hov how hvw ?_
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_of_sourceSectorCap_residualMomentBranchSummand_sum_bound
      (n := n) (v := v) (w := w) hβ Ω e0 hcap hbudget


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_finite_image_count_mul_bound
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
        (∑ m' ∈ Ω.image
            (fun m => Function.update m e0 (m e0 + 1)),
          ((m' e0 : ℕ) : ℝ) *
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
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
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul
        (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw).trans
      (hfinite Ω)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_finite_image_count_mul_bound
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
            (∑ m' ∈ Ω.image
                (fun m => Function.update m e0 (m e0 + 1)),
              ((m' e0 : ℕ) : ℝ) *
                doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w
                  m') ≤
              C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_finite_image_count_mul_bound
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (hfinite e0 hedge)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_selectedCopySplitBound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
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
            (∑ m' ∈ Ω.image
                (fun m => Function.update m e0 (m e0 + 1)),
              ((m' e0 : ℕ) : ℝ) *
                doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w
                  m') ≤
              doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_finite_image_count_mul_bound
    (n := n) (v := v) (w := w) hβ hvwedge hwwedge hheight hadj
    hfinite

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_decrementImageBranchSum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
                (Function.update m e0 (m e0 + 1))) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_finite_image_count_mul_bound
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (fun Ω =>
        doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_decrementImageBranchSum_bound
          (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw
          (habsorb e0 hedge Ω))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_branchCardSourcePairSummand_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_decrementImageBranchSum_bound
      (n := n) (v := v) (w := w) hβ hvwedge hwwedge hheight hadj ?_
  intro e0 hedge Ω
  calc
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1))) =
        ∑ m ∈ Ω,
          doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m := by
      exact
        doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_finset_sum_eq_branchCardSourcePairSummand
          (β := β) (n := n) (v := v) (w := w) Ω e0
    _ ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) :=
      habsorb e0 hedge Ω

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_filter_switchedSourceSectorResidualMomentBranchSummand_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hbudget :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω.filter
              (fun m =>
                Sharpness.RandomCurrent.sources
                    (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
                      (Function.update m e0 (m e0 + 1)))
                    (Finset.univ :
                      Finset (Sharpness.FluxEdgeCopy.Copy
                        (FK.boxGraph 3 (2 * n))
                        (Function.update m e0 (m e0 + 1)))) =
                  doubledBoxOriginToInnerEndpointSource n w),
              (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
                doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤
              β *
                (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                  Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n w)
                    (doubledBoxInnerPairSource n v w))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_finite_image_count_mul_bound
      (n := n) (v := v) (w := w) e0 hβ.le hedge hov how hvw
      (fun Ω =>
        doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_selectedCopySplitBound_of_filter_switchedSourceSectorResidualMomentBranchSummand_sum_bound
          (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw
          (hbudget e0 hedge Ω))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w
                e0 m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_branchCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) hβ hvwedge hwwedge hheight hadj ?_
  intro e0 hedge Ω
  exact
    (doubledBoxSelectedCopyBranchCardSourcePairSummand_finset_sum_le_totalPairCardSourcePairSummand
      (n := n) (v := v) (w := w) hβ Ω e0).trans
      (habsorb e0 hedge Ω)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_unweightedSelectedCopyTotalPairCardSourcePairBound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          doubledBoxUnweightedSelectedCopyTotalPairCardSourcePairBound β n v w e0) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) hβ hvwedge hwwedge hheight hadj ?_
  intro e0 hedge Ω
  exact hbound e0 hedge Ω

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_sourceSectorCap_residualMomentBranchSummand_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hcap :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            ∀ m ∈ Ω,
              (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) ≤ C)
    (hbudget :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            C * (∑ m ∈ Ω,
              doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤
              β *
                (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                  Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n w)
                    (doubledBoxInnerPairSource n v w))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) hβ.le hvwedge hwwedge hheight hadj ?_
  intro e0 hedge Ω
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_of_sourceSectorCap_residualMomentBranchSummand_sum_bound
      (n := n) (v := v) (w := w) hβ Ω e0
      (hcap e0 hedge Ω) (hbudget e0 hedge Ω)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_tsum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w
              e0 m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w
              e0 m) ≤
            doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
              Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_bound
      (n := n) (v := v) (w := w) hβ hvwedge hwwedge hheight hadj ?_
  intro e0 hedge Ω
  calc
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w
            e0 m :=
      (hsum e0 hedge).sum_le_tsum Ω
        (fun m _hm =>
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand_nonneg
            (n := n) (v := v) (w := w) hβ e0 m)
    _ ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) :=
      hbound e0 hedge

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandBound_of_strictSectorPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
                (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0 m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorPredecessor3 v hvwedge hlt))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorPredecessor3 v hvwedge hlt))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorPredecessor3 v hvwedge hlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandBound_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
                m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandBound_of_diagonalPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0
                m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))
                  (doubledBoxInnerPairSource n v
                    (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_bound
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandTsumBound_of_strictSectorPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
              (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0 m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
              (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0 m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorPredecessor3 v hvwedge hlt))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorPredecessor3 v hvwedge hlt))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorPredecessor3 v hvwedge hlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_tsum_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)
    hsum hbound

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandTsumBound_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_tsum_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    hsum hbound

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_sourceSectorResidualMomentBranchSummandTsumBound_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxSourceSectorResidualMomentBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSourceSectorResidualMomentBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
              β *
                (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                  Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                    (doubledBoxInnerPairSource n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandTsumBound_of_strictSectorYPredecessor3
    (β := β) (n := n) (v := v) hβ.le hvwedge hlt hypos
    (fun e0 hedge =>
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand_summable_of_sourceSectorResidualMomentBranchSummand_summable
        (β := β) (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        hβ e0 (hsum e0 hedge))
    (fun e0 hedge =>
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand_tsum_le_of_sourceSectorResidualMomentBranchSummand_tsum_bound
        (β := β) (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        hβ e0 (hbound e0 hedge))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_sourceSectorCapResidualMomentBranchSummandBound_of_strictSectorYPredecessor3
    {β C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hcap :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            ∀ m ∈ Ω,
              (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) ≤ C)
    (hbudget :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            C * (∑ m ∈ Ω,
              doubledBoxResidualMomentBranchSummand β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
                m) ≤
              β *
                (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                  Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                    (doubledBoxInnerPairSource n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_sourceSectorCap_residualMomentBranchSummand_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    hcap hbudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_sourceSectorCapResidualMomentBranchSummandTsumBound_of_strictSectorYPredecessor3
    {β C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (hC : 0 ≤ C)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hcap :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) ≤ C)
    (hbudget :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          C * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              m) ≤
            β *
              (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_sourceSectorCapResidualMomentBranchSummandBound_of_strictSectorYPredecessor3
      (β := β) (C := C) (n := n) (v := v) hβ hvwedge hlt hypos ?_ ?_
  · intro e0 hedge Ω m _hm
    exact hcap e0 hedge m
  · intro e0 hedge Ω
    have hsum_le :
        (∑ m ∈ Ω,
          doubledBoxResidualMomentBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m) ≤
          ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              m :=
      (doubledBoxResidualMomentBranchSummand_summable β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0).sum_le_tsum
        Ω
        (fun m _hm =>
          doubledBoxResidualMomentBranchSummand_nonneg
            (n := n) (v := v)
            (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            hβ.le e0 m)
    exact (mul_le_mul_of_nonneg_left hsum_le hC).trans (hbudget e0 hedge)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandTsumBound_of_diagonalPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0
              m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0
              m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))
                  (doubledBoxInnerPairSource n v
                    (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_totalPairCardSourcePairSummand_tsum_bound
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)
    hsum hbound

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_branchCardSourcePairSummandBound_of_strictSectorPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyBranchCardSourcePairSummand β n v
                (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0 m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorPredecessor3 v hvwedge hlt))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorPredecessor3 v hvwedge hlt))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorPredecessor3 v hvwedge hlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_branchCardSourcePairSummand_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_branchCardSourcePairSummandBound_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyBranchCardSourcePairSummand β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
                m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_branchCardSourcePairSummand_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_filter_switchedSourceSectorResidualMomentBranchSummandBound_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hbudget :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω.filter
              (fun m =>
                Sharpness.RandomCurrent.sources
                    (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
                      (Function.update m e0 (m e0 + 1)))
                    (Finset.univ :
                      Finset (Sharpness.FluxEdgeCopy.Copy
                        (FK.boxGraph 3 (2 * n))
                        (Function.update m e0 (m e0 + 1)))) =
                  doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)),
              (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
                doubledBoxResidualMomentBranchSummand β n v
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
                  m) ≤
              β *
                (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                  Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                    (doubledBoxInnerPairSource n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_filter_switchedSourceSectorResidualMomentBranchSummand_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    hbudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_branchCardSourcePairSummandBound_of_diagonalPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyBranchCardSourcePairSummand β n v
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0
                m) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))
                  (doubledBoxInnerPairSource n v
                    (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_branchCardSourcePairSummand_bound
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_decrementImageBranchSum_tsum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
              (Function.update m e0 (m e0 + 1))))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
              (Function.update m e0 (m e0 + 1))) ≤
            doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
              Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_decrementImageBranchSum_bound
      (n := n) (v := v) (w := w) hβ hvwedge hwwedge hheight hadj ?_
  intro e0 hedge Ω
  calc
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1))) ≤
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
            (Function.update m e0 (m e0 + 1)) :=
      (hsum e0 hedge).sum_le_tsum Ω
        (fun m _hm =>
          doubledBoxSelectedCopyDecrementImageBranchSum_nonneg
            (n := n) (v := v) (w := w) hβ e0
            (Function.update m e0 (m e0 + 1)))
    _ ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) :=
      hbound e0 hedge

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_selectedCopySplitBound_of_strictSectorPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hfinite :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m' ∈ Ω.image
                (fun m => Function.update m e0 (m e0 + 1)),
              ((m' e0 : ℕ) : ℝ) *
                doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n
                  (boxVertStrictSectorPredecessor3 v hvwedge hlt) m') ≤
              doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorPredecessor3 v hvwedge hlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_selectedCopySplitBound
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)
    hfinite

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_selectedCopySplitBound_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hfinite :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m' ∈ Ω.image
                (fun m => Function.update m e0 (m e0 + 1)),
              ((m' e0 : ℕ) : ℝ) *
                doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                  m') ≤
              doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_selectedCopySplitBound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    hfinite

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_selectedCopySplitBound_of_diagonalPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hfinite :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m' ∈ Ω.image
                (fun m => Function.update m e0 (m e0 + 1)),
              ((m' e0 : ℕ) : ℝ) *
                doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n
                  (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
                  m') ≤
              doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_selectedCopySplitBound
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)
    hfinite

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_decrementImageBranchSumBound_of_strictSectorPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyDecrementImageBranchSum β n v
                (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0
                (Function.update m e0 (m e0 + 1))) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorPredecessor3 v hvwedge hlt))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorPredecessor3 v hvwedge hlt))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorPredecessor3 v hvwedge hlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_decrementImageBranchSum_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_decrementImageBranchSumBound_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyDecrementImageBranchSum β n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
                (Function.update m e0 (m e0 + 1))) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  (doubledBoxInnerPairSource n v
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_decrementImageBranchSum_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_decrementImageBranchSumBound_of_diagonalPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (habsorb :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
            (∑ m ∈ Ω,
              doubledBoxSelectedCopyDecrementImageBranchSum β n v
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0
                (Function.update m e0 (m e0 + 1))) ≤
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))
                  (doubledBoxInnerPairSource n v
                    (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
        (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_decrementImageBranchSum_bound
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)
    habsorb

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentBound_of_strictSectorPredecessor3
    {β C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hfinite :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
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
                    (doubledBoxOriginToInnerEndpointSource n
                      (boxVertStrictSectorPredecessor3 v hvwedge hlt))
                    (doubledBoxInnerPairSource n v
                      (boxVertStrictSectorPredecessor3 v hvwedge hlt)) m) ≤
              C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_finite_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)
    hfinite

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentBound_of_strictSectorYPredecessor3
    {β C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hfinite :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
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
                    (doubledBoxOriginToInnerEndpointSource n
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                    (doubledBoxInnerPairSource n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                    m) ≤
              C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_finite_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    hfinite

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentBound_of_diagonalPredecessor3
    {β C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hfinite :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
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
                    (doubledBoxOriginToInnerEndpointSource n
                      (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))
                    (doubledBoxInnerPairSource n v
                      (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt))
                    m) ≤
              C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_finite_bound
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)
    hfinite

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentTsumBound_of_strictSectorPredecessor3
    {β C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentBranchSummand β n v
              (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0 m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentBranchSummand β n v
              (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0 m) ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_tsum_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)
    hsum hbound

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentTsumBound_of_strictSectorYPredecessor3
    {β C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_tsum_bound
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    hsum hbound

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentTsumBound_of_diagonalPredecessor3
    {β C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentBranchSummand β n v
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0 m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentBranchSummand β n v
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0 m) ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_tsum_bound
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)
    hsum hbound

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentBranchTsumBounds_of_strictSectorPredecessor3
    {β Cempty Cinner C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hempty :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m))
    (hinner :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentInnerPairBranchSummand β n v
              (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0 m))
    (hempty_bound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤ Cempty)
    (hinner_bound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorPredecessor3 v hvwedge hlt)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentInnerPairBranchSummand β n v
              (boxVertStrictSectorPredecessor3 v hvwedge hlt) e0 m) ≤ Cinner)
    (hbudget : Cempty + Cinner ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_branch_tsum_bounds
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)
    hempty hinner hempty_bound hinner_bound hbudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentBranchTsumBounds_of_strictSectorYPredecessor3
    {β Cempty Cinner C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (hempty :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m))
    (hinner :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentInnerPairBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m))
    (hempty_bound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤ Cempty)
    (hinner_bound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentInnerPairBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤ Cinner)
    (hbudget : Cempty + Cinner ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_branch_tsum_bounds
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)
    hempty hinner hempty_bound hinner_bound hbudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_residualMomentBranchTsumBounds_of_diagonalPredecessor3
    {β Cempty Cinner C : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hempty :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m))
    (hinner :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentInnerPairBranchSummand β n v
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0 m))
    (hempty_bound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤ Cempty)
    (hinner_bound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentInnerPairBranchSummand β n v
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt) e0 m) ≤ Cinner)
    (hbudget : Cempty + Cinner ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_branch_tsum_bounds
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)
    hempty hinner hempty_bound hinner_bound hbudget


theorem edgeCopySourcePairEmptyCollapsedSum_le_of_term_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (hterm :
      ∀ m : ↥G.edgeFinset → ℕ,
        edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
          edgeCopySourcePairEmptyCollapsedTerm G β J B m) :
    edgeCopySourcePairEmptyCollapsedSum G β J A ≤
      edgeCopySourcePairEmptyCollapsedSum G β J B := by
  rw [edgeCopySourcePairEmptyCollapsedSum_eq_tsum_term G β J A]
  rw [edgeCopySourcePairEmptyCollapsedSum_eq_tsum_term G β J B]
  exact
    (edgeCopySourcePairEmptyCollapsedTerm_summable G β J A).tsum_le_tsum
      hterm
      (edgeCopySourcePairEmptyCollapsedTerm_summable G β J B)


theorem edgeCopySourcePairEmptyCollapsedSum_le_of_reindex_term_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (φ : (↥G.edgeFinset → ℕ) → (↥G.edgeFinset → ℕ))
    (hφ : Function.Injective φ)
    (hterm :
      ∀ m : ↥G.edgeFinset → ℕ,
        edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
          edgeCopySourcePairEmptyCollapsedTerm G β J B (φ m)) :
    edgeCopySourcePairEmptyCollapsedSum G β J A ≤
      edgeCopySourcePairEmptyCollapsedSum G β J B := by
  rw [edgeCopySourcePairEmptyCollapsedSum_eq_tsum_term G β J A]
  rw [edgeCopySourcePairEmptyCollapsedSum_eq_tsum_term G β J B]
  have hA :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        edgeCopySourcePairEmptyCollapsedTerm G β J A m) :=
    edgeCopySourcePairEmptyCollapsedTerm_summable G β J A
  have hB :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        edgeCopySourcePairEmptyCollapsedTerm G β J B m) :=
    edgeCopySourcePairEmptyCollapsedTerm_summable G β J B
  have hBcomp :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        edgeCopySourcePairEmptyCollapsedTerm G β J B (φ m)) :=
    hB.comp_injective hφ
  calc
    (∑' m : ↥G.edgeFinset → ℕ,
        edgeCopySourcePairEmptyCollapsedTerm G β J A m)
        ≤
      ∑' m : ↥G.edgeFinset → ℕ,
        edgeCopySourcePairEmptyCollapsedTerm G β J B (φ m) :=
      hA.tsum_le_tsum hterm hBcomp
    _ ≤
      ∑' m : ↥G.edgeFinset → ℕ,
        edgeCopySourcePairEmptyCollapsedTerm G β J B m :=
      Summable.tsum_le_tsum_of_inj φ hφ
        (fun m _hm =>
          edgeCopySourcePairEmptyCollapsedTerm_nonneg G β J B hβ hJ m)
        (fun _ => le_rfl)
        hBcomp hB


theorem edgeCopySourcePairEmptyCollapsedSum_le_of_reindex_edgeEquivVertexEquiv_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) {A B : Finset V}
    (hβ : 0 ≤ β)
    (f : (↥G.edgeFinset → ℕ) → (↥G.edgeFinset → ℕ))
    (hf : Function.Injective f)
    (φ : (↥G.edgeFinset → ℕ) → V ≃ V)
    (σ :
      (m : ↥G.edgeFinset → ℕ) →
        ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ m e, f m (σ m e) = m e)
    (hends : ∀ m e, (σ m e).1 = Sym2.map (φ m) e.1)
    (hAB : ∀ m, A.map (φ m).toEmbedding = B) :
    edgeCopySourcePairEmptyCollapsedSum G β (fun _ => 1) A ≤
      edgeCopySourcePairEmptyCollapsedSum G β (fun _ => 1) B :=
  edgeCopySourcePairEmptyCollapsedSum_le_of_reindex_term_le
    G β (fun _ => 1) hβ (by intro e; norm_num) f hf
    (fun m =>
      edgeCopySourcePairEmptyCollapsedTerm_le_of_edgeEquivVertexEquiv_homogeneous
        G β m (f m) hβ (φ m) (σ m) (hm m) (hends m) (hAB m))


theorem sourcePairSum_empty_eq_edgeCopySourcePairEmptyCollapsedSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Sharpness.sourcePairSum G β J A (∅ : Finset V) =
      edgeCopySourcePairEmptyCollapsedSum G β J A := by
  rw [sourcePairSum_eq_edgeCopySourcePairSum]
  rw [edgeCopySourcePairSum_empty_eq_collapsed]


theorem sourcePairSum_empty_le_of_edgeCopyCollapsedSum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (hcopy :
      edgeCopySourcePairEmptyCollapsedSum G β J A ≤
        edgeCopySourcePairEmptyCollapsedSum G β J B) :
    Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤
      Sharpness.sourcePairSum G β J B (∅ : Finset V) := by
  rw [sourcePairSum_empty_eq_edgeCopySourcePairEmptyCollapsedSum G β J A]
  rw [sourcePairSum_empty_eq_edgeCopySourcePairEmptyCollapsedSum G β J B]
  exact hcopy


theorem doubledBoxOriginToInnerEndpointSourcePairEmptySum_eq_edgeCopyCollapsedSum
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n} :
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v =
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v := by
  exact
    sourcePairSum_empty_eq_edgeCopySourcePairEmptyCollapsedSum
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)


theorem doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_edgeCopyCollapsedSum_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hcopy :
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n w) :
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w := by
  rw [doubledBoxOriginToInnerEndpointSourcePairEmptySum_eq_edgeCopyCollapsedSum]
  rw [doubledBoxOriginToInnerEndpointSourcePairEmptySum_eq_edgeCopyCollapsedSum]
  exact hcopy


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_term_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hterm :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n w :=
  edgeCopySourcePairEmptyCollapsedSum_le_of_term_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1) hterm


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_reindex_term_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (φ :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hφ : Function.Injective φ)
    (hterm :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w (φ m)) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n w :=
  edgeCopySourcePairEmptyCollapsedSum_le_of_reindex_term_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
    hβ (by intro e; norm_num) φ hφ hterm


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_reindex_edgeEquivVertexEquiv
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (f :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hf : Function.Injective f)
    (φ :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ m e, f m (σ m e) = m e)
    (hends : ∀ m e, (σ m e).1 = Sym2.map (φ m) e.1)
    (hsrc :
      ∀ m,
        (doubledBoxOriginToInnerEndpointSource n v).map
            (φ m).toEmbedding =
          doubledBoxOriginToInnerEndpointSource n w) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n w :=
  edgeCopySourcePairEmptyCollapsedSum_le_of_reindex_edgeEquivVertexEquiv_homogeneous
    (FK.boxGraph 3 (2 * n)) β hβ f hf φ σ hm hends hsrc

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_reindex_edgeEquivVertexEquiv_maps_origin_endpoint
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (f :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hf : Function.Injective f)
    (φ :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ m e, f m (σ m e) = m e)
    (hends : ∀ m e, (σ m e).1 = Sym2.map (φ m) e.1)
    (horigin :
      ∀ m, φ m (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (hend :
      ∀ m,
        φ m (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) =
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n w :=
  doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_reindex_edgeEquivVertexEquiv
    hβ f hf φ σ hm hends
    (fun m =>
      doubledBoxOriginToInnerEndpointSource_map_eq_of_maps_origin_endpoint
        (φ m) (horigin m) (hend m))


theorem currentSum_le_of_sourcePairSum_empty_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (hpair :
      Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤
        Sharpness.sourcePairSum G β J B (∅ : Finset V)) :
    Sharpness.currentSum G β J A ≤ Sharpness.currentSum G β J B := by
  rw [Sharpness.sourcePairSum_eq_mul, Sharpness.sourcePairSum_eq_mul] at hpair
  exact le_of_mul_le_mul_right hpair (currentSum_empty_pos G β J)


theorem expectationJ_le_of_sourcePairSum_empty_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (hpair :
      Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤
        Sharpness.sourcePairSum G β J B (∅ : Finset V)) :
    Sharpness.expectationJ G β J A ≤ Sharpness.expectationJ G β J B :=
  expectationJ_le_of_currentSum_le G β J
    (currentSum_le_of_sourcePairSum_empty_le G β J hpair)


theorem doubledBoxOriginToInnerEndpointExpectationJ_le_of_currentSum_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hraw :
      doubledBoxOriginToInnerEndpointCurrentSum β n v ≤
        doubledBoxOriginToInnerEndpointCurrentSum β n w) :
    Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) ≤
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w) :=
  expectationJ_le_of_currentSum_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1) hraw


theorem doubledBoxOriginToInnerEndpointCurrentSum_le_of_sourcePairEmptySum_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpair :
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    doubledBoxOriginToInnerEndpointCurrentSum β n v ≤
      doubledBoxOriginToInnerEndpointCurrentSum β n w :=
  currentSum_le_of_sourcePairSum_empty_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1) hpair


theorem doubledBoxOriginToInnerEndpointExpectationJ_le_of_sourcePairEmptySum_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpair :
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) ≤
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w) :=
  expectationJ_le_of_sourcePairSum_empty_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1) hpair

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitAbsorption
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (habsorb :
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w := by
  have hmul :
      β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w := by
    calc
      β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v =
          β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v := by
            rw [doubledBoxOriginToInnerEndpointSourcePairEmptySum_eq_edgeCopyCollapsedSum]
      _ ≤ doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w :=
        hpaid
      _ ≤ β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w :=
        habsorb
  exact le_of_mul_le_mul_left hmul hβpos

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointCurrentSum_le_of_selectedCopySplitAbsorption
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (habsorb :
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    doubledBoxOriginToInnerEndpointCurrentSum β n v ≤
      doubledBoxOriginToInnerEndpointCurrentSum β n w :=
  doubledBoxOriginToInnerEndpointCurrentSum_le_of_sourcePairEmptySum_le
    (doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitAbsorption
      hβpos hpaid habsorb)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitAbsorption
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (habsorb :
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) ≤
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w) :=
  doubledBoxOriginToInnerEndpointExpectationJ_le_of_sourcePairEmptySum_le
    (doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitAbsorption
      hβpos hpaid habsorb)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitSourcePairSplit
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (hsplit :
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w :=
  doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitAbsorption
    hβpos hpaid
    (doubledBoxOriginToInnerEndpointSelectedCopySplitBound_le_beta_mul_sourcePairEmptySum_of_sourcePairSplit_le
      (le_of_lt hβpos) n v w
      (by
        simpa [doubledBoxOriginToInnerEndpointSourcePairSplitScalar] using
          hsplit))

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointCurrentSum_le_of_selectedCopySplitSourcePairSplit
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (hsplit :
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    doubledBoxOriginToInnerEndpointCurrentSum β n v ≤
      doubledBoxOriginToInnerEndpointCurrentSum β n w :=
  doubledBoxOriginToInnerEndpointCurrentSum_le_of_sourcePairEmptySum_le
    (doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitSourcePairSplit
      hβpos hpaid hsplit)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitSourcePairSplit
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (hsplit :
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) ≤
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w) :=
  doubledBoxOriginToInnerEndpointExpectationJ_le_of_sourcePairEmptySum_le
    (doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitSourcePairSplit
      hβpos hpaid hsplit)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitSourcePairSplitScalar
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (hsplit :
      doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w :=
  doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitAbsorption
    hβpos hpaid
    (doubledBoxOriginToInnerEndpointSelectedCopySplitBound_le_beta_mul_sourcePairEmptySum_of_sourcePairSplit_le
      hβpos.le n v w hsplit)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitSourcePairSplitScalar
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (hsplit :
      doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) ≤
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w) :=
  doubledBoxOriginToInnerEndpointExpectationJ_le_of_sourcePairEmptySum_le
    (doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_selectedCopySplitSourcePairSplitScalar
      hβpos hpaid hsplit)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitExpectationJSplit
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (hJ :
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v) +
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w) *
          Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w) ≤
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)) :
    Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) ≤
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w) :=
  doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitSourcePairSplitScalar
    hβpos hpaid
    (doubledBoxOriginToInnerEndpointSourcePairSplitScalar_le_sourcePairEmptySum_of_expectationJ_split_le
      hJ)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitExpectationJRatioGap
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpaid :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w)
    (hpos :
      0 < Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w))
    (hratio :
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v) /
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w) +
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxInnerPairSource n v w) ≤ 1) :
    Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) ≤
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w) :=
  doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitSourcePairSplitScalar
    hβpos hpaid
    (doubledBoxOriginToInnerEndpointSourcePairSplitScalar_le_sourcePairEmptySum_of_expectationJ_ratio_gap
      hpos hratio)


theorem freeQ2DoubledFullOriginConnProb_eq_expectationJ
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n) :
    freeQ2DoubledFullOriginConnProb β hβpos n v =
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v) := by
  unfold freeQ2DoubledFullOriginConnProb
  unfold doubledBoxOriginToInnerEndpointSource
  calc
    ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 (2 * n) (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
        =
      (∑ σ : ConfigSpace (FK.boxVerts 3 (2 * n)),
        Ising.isingProb (FK.boxGraph 3 (2 * n)) β 0 σ *
          (Ising.spin σ (IsingFK.boxOrigin 3 (2 * n)) *
            Ising.spin σ
              (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))) := by
          exact
            (finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos
              3 (2 * n) hβpos
              (IsingFK.boxOrigin 3 (2 * n))
              (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)).symm
    _ =
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (({IsingFK.boxOrigin 3 (2 * n)} : Finset (FK.boxVerts 3 (2 * n))) ∆
          {FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v}) := by
          exact
            finiteIsingTwoPoint_boxGraph_eq_expectationJ_symmDiff
              3 (2 * n) β
              (IsingFK.boxOrigin 3 (2 * n))
              (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)


theorem freeQ2DoubledFullOriginConnProb_le_of_expectationJ_le
    {β : ℝ} {hβpos : 0 < β} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hJ :
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v) ≤
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)) :
    freeQ2DoubledFullOriginConnProb β hβpos n v ≤
    freeQ2DoubledFullOriginConnProb β hβpos n w := by
  rw [freeQ2DoubledFullOriginConnProb_eq_expectationJ hβpos n v,
    freeQ2DoubledFullOriginConnProb_eq_expectationJ hβpos n w]
  exact hJ


end Exact3D
end StatMech
