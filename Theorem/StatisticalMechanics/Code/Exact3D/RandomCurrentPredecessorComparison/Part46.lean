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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part44
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxAllComplementWitnessCardWeightFactor_eq_sourceSector_card_mul_weight
    (β : ℝ) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) := by
  dsimp [doubledBoxAllComplementWitnessCardWeightFactor]
  rw [← Finset.sum_mul]
  rw [← Nat.cast_sum]
  rw [← edgeCopySourceSector_card_eq_sum_sourcePairWitnesses_card]

set_option linter.style.longLine false in


theorem doubledBoxAllComplementWitnessCardWeightFactor_nonneg
    {β : ℝ} {n : ℕ} {w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m := by
  rw [doubledBoxAllComplementWitnessCardWeightFactor_eq_sourceSector_card_mul_weight]
  exact
    mul_nonneg (by positivity)
      (weight_ofEdgeFun_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        hβ (by intro e; norm_num) m)

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_allComplementSourcePairSummand_increment_eq_beta_mul_doubledBoxAllComplementWitnessCardWeightFactor
    (β : ℝ) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    (((m e0 + 1 : ℕ) : ℝ) *
      (∑ B : Finset (FK.boxVerts 3 (2 * n)),
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w) B
          (Function.update m e0 (m e0 + 1)))) =
      β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  have h :=
    edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment_eq_betaJ_mul_sum_sourcePairWitnesses_card_mul_weight
      G β (fun _ => 1) A m e0
  simpa [doubledBoxAllComplementWitnessCardWeightFactor, G, A] using h

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_beta_mul_allComplementWitnessCardWeightFactor
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
          (Function.update m e0 (m e0 + 1))) *
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
  simpa [doubledBoxAllComplementWitnessCardWeightFactor] using
    weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_beta_mul_allComplementWitnessCardWeight_sum
      β n v w e0 m

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_beta_mul_allComplementWitnessCardWeightFactor
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      ∑ m ∈ Ω,
        (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) *
          (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) := by
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_beta_mul_allComplementWitnessCardWeightFactor
      β n v w e0 m

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_summable
    (β : ℝ) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) := by
  have hleft :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        (((m e0 + 1 : ℕ) : ℝ) *
          ∑ B : Finset (FK.boxVerts 3 (2 * n)),
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w) B
              (Function.update m e0 (m e0 + 1)))) :=
    summable_edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w) e0
  refine hleft.congr ?_
  intro m
  exact
    edgeMultiplicitySucc_mul_allComplementSourcePairSummand_increment_eq_beta_mul_doubledBoxAllComplementWitnessCardWeightFactor
      β n w e0 m

set_option linter.style.longLine false in


theorem doubledBoxAllComplementWitnessCardWeightFactor_summable_of_pos_beta
    {β : ℝ} (hβ : 0 < β) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) := by
  have hbeta :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) :=
    beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_summable
      β n w e0
  have hscaled :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        β⁻¹ * (β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m)) :=
    Summable.mul_left β⁻¹ hbeta
  refine hscaled.congr ?_
  intro m
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_tsum_le_sum_sourcePairSum_two_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    β *
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) ≤
      ∑ B : Finset (FK.boxVerts 3 (2 * n)),
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B := by
  have hrewrite :
      β *
        (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) =
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          (((m e0 + 1 : ℕ) : ℝ) *
            ∑ B : Finset (FK.boxVerts 3 (2 * n)),
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B
                (Function.update m e0 (m e0 + 1))) := by
    rw [← tsum_mul_left]
    exact
      tsum_congr fun m =>
        (edgeMultiplicitySucc_mul_allComplementSourcePairSummand_increment_eq_beta_mul_doubledBoxAllComplementWitnessCardWeightFactor
          β n w e0 m).symm
  rw [hrewrite]
  exact
    edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment_tsum_le_sum_sourcePairSum_two_beta
      (FK.boxGraph 3 (2 * n)) hβ
      (doubledBoxOriginToInnerEndpointSource n w) e0

set_option linter.style.longLine false in


theorem doubledBoxAllComplementWitnessCardWeightFactor_tsum_le_inv_beta_mul_sum_sourcePairSum_two_beta
    {β : ℝ} (hβ : 0 < β) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) ≤
      β⁻¹ *
        ∑ B : Finset (FK.boxVerts 3 (2 * n)),
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B := by
  have hmul :=
    beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_tsum_le_sum_sourcePairSum_two_beta
      hβ.le n w e0
  calc
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) =
        β⁻¹ *
          (β *
            (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
              doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]
    _ ≤
        β⁻¹ *
          ∑ B : Finset (FK.boxVerts 3 (2 * n)),
            edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B := by
      exact mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hβ.le)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_finset_sum_le_sum_sourcePairSum_two_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    β *
      (∑ m ∈ Ω,
        doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) ≤
      ∑ B : Finset (FK.boxVerts 3 (2 * n)),
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B := by
  calc
    β *
      (∑ m ∈ Ω,
        doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) =
        ∑ m ∈ Ω,
          β * doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m := by
      rw [Finset.mul_sum]
    _ =
        ∑ m ∈ Ω,
          (((m e0 + 1 : ℕ) : ℝ) *
            ∑ B : Finset (FK.boxVerts 3 (2 * n)),
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B
                (Function.update m e0 (m e0 + 1))) := by
      refine Finset.sum_congr rfl ?_
      intro m _hm
      rw [
        ← edgeMultiplicitySucc_mul_allComplementSourcePairSummand_increment_eq_beta_mul_doubledBoxAllComplementWitnessCardWeightFactor]
    _ ≤
        ∑ B : Finset (FK.boxVerts 3 (2 * n)),
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B :=
      edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment_finset_sum_le_sum_sourcePairSum_two_beta
        (FK.boxGraph 3 (2 * n)) hβ
        (doubledBoxOriginToInnerEndpointSource n w) e0 Ω

set_option linter.style.longLine false in


theorem doubledBoxAllComplementWitnessCardWeightFactor_finset_sum_le_inv_beta_mul_sum_sourcePairSum_two_beta
    {β : ℝ} (hβ : 0 < β) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) ≤
      β⁻¹ *
        ∑ B : Finset (FK.boxVerts 3 (2 * n)),
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B := by
  have hmul :=
    beta_mul_doubledBoxAllComplementWitnessCardWeightFactor_finset_sum_le_sum_sourcePairSum_two_beta
      hβ.le n w e0 Ω
  calc
    (∑ m ∈ Ω,
      doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m) =
        β⁻¹ *
          (β *
            (∑ m ∈ Ω,
              doubledBoxAllComplementWitnessCardWeightFactor β n w e0 m)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]
    _ ≤
        β⁻¹ *
          ∑ B : Finset (FK.boxVerts 3 (2 * n)),
            edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w) B := by
      exact mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hβ.le)

end Exact3D
end StatMech
