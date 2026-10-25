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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part45
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_tsum_le_beta_of_allComplementTwoBetaMassCap
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hcap : doubledBoxAllComplementTwoBetaMassCap β n w) :
    β *
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) ≤ β :=
  (beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_tsum_le_sum_sourcePairSum_two_beta
    hβ n w e0).trans
    (by simpa [doubledBoxAllComplementTwoBetaMassCap] using hcap)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_finset_sum_le_beta_of_allComplementTwoBetaMassCap
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hcap : doubledBoxAllComplementTwoBetaMassCap β n w) :
    β *
      (∑ m ∈ Ω,
        doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) ≤ β :=
  (beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_finset_sum_le_sum_sourcePairSum_two_beta
    hβ n w e0 Ω).trans
    (by simpa [doubledBoxAllComplementTwoBetaMassCap] using hcap)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyBranchSourcePairSummand_add_le_sourcePairSplitSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  have hleft :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
    simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum,
      sourcePairSum_eq_edgeCopySourcePairSum] using
      edgeCopySourcePairSummand_le_edgeCopySourcePairSum
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  have hright :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
    simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
      edgeCopySourcePairSummand_le_edgeCopySourcePairSum
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  exact add_le_add hleft hright

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyBranchSourcePairSummand_add_le_sourcePairSplitScalar
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m ≤
      doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w := by
  simpa [doubledBoxOriginToInnerEndpointSourcePairSplitScalar] using
    doubledBoxSelectedCopyBranchSourcePairSummand_add_le_sourcePairSplitSum
      hβ n v w m

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairSplitSum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n) :
    0 ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) := by
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

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairEmptySum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v : FK.boxVerts 3 n) :
    0 ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum,
    sourcePairSum_eq_edgeCopySourcePairSum] using
    edgeCopySourcePairSum_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) hβ
      (by intro e; norm_num)

set_option linter.style.longLine false in


theorem doubledBoxInnerPairSourcePairSum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n) :
    0 ≤ Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) := by
  simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
    edgeCopySourcePairSum_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) hβ
      (by intro e; norm_num)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_singleton_selectedEdgeCopies_sum_le_sourcePairSplitSum
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ m ∈ doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  have hsum :
      (∑ m ∈ doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
        0 := by
    simp [doubledBoxSelectedEdgeCopiesSingletonCutoff,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand_selectedEdgeCopies_eq_zero
        β e0 k hedge hov how]
  rw [hsum]
  exact doubledBoxOriginToInnerEndpointSourcePairSplitSum_nonneg hβ n v w

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_allComplementTwoBeta_mul_sourcePairSplitSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
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
  have hfactor_bound :
      (∑ m ∈ Ω,
        β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) ≤
        T := by
    dsimp [T]
    calc
      (∑ m ∈ Ω,
        β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) =
          β *
            (∑ m ∈ Ω,
              doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) := by
        rw [Finset.mul_sum]
      _ ≤
          ∑ B : Finset (FK.boxVerts 3 (2 * n)),
            edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B :=
        beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_finset_sum_le_sum_sourcePairSum_two_beta
          hβ n w e0 Ω
  calc
    (∑ m ∈ Ω,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m)
        =
      ∑ m ∈ Ω,
        (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) *
          (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) := by
      exact
        weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_beta_mul_allComplementWitnessCardWeightFactor
          β n v w Ω e0
    _ ≤
      ∑ m ∈ Ω,
        (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) * S := by
      refine Finset.sum_le_sum ?_
      intro m _hm
      have hfactor :
          0 ≤ β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m :=
        mul_nonneg hβ
          (doubledBoxAllComplementWitnessCardWeightFactor_nonneg hβ e0 m)
      exact
        mul_le_mul_of_nonneg_left
          (doubledBoxSelectedCopyBranchSourcePairSummand_add_le_sourcePairSplitSum
            hβ n v w m) hfactor
    _ =
      (∑ m ∈ Ω,
        β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) * S := by
      rw [Finset.sum_mul]
    _ ≤ T * S := by
      exact mul_le_mul_of_nonneg_right hfactor_bound hS_nonneg
    _ =
      (∑ B : Finset (FK.boxVerts 3 (2 * n)),
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B) *
        (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) := by
      rfl

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_selectedCopySplitBound_of_allComplementTwoBeta_le_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hall :
      (∑ B : Finset (FK.boxVerts 3 (2 * n)),
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B) ≤ β) :
    (∑ m ∈ Ω,
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
      (∑ m ∈ Ω,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1))) *
          doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        T * S := by
    simpa [T, S] using
      weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_allComplementTwoBeta_mul_sourcePairSplitSum
        (n := n) (v := v) (w := w) hβ Ω e0
  calc
    (∑ m ∈ Ω,
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


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_selectedCopySplitBound_of_allComplementTwoBetaMassCap
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hcap : doubledBoxAllComplementTwoBetaMassCap β n w) :
    (∑ m ∈ Ω,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w :=
  weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_selectedCopySplitBound_of_allComplementTwoBeta_le_beta
    (n := n) (v := v) (w := w) hβ Ω e0
    (by simpa [doubledBoxAllComplementTwoBetaMassCap] using hcap)

end Exact3D
end StatMech
