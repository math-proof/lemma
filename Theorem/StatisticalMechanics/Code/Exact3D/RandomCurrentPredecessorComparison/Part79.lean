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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part71
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_selectedEdge_eq
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
        β n v w e0 e0 m =
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v w e0 m := rfl

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_selectedEdge_eq
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
        β n v w e0 e0 m =
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m := rfl

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_selectedEdge_eq
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
        β n v w e0 e0 m =
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand
        β n v w e0 m := rfl

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_selectedEdge_eq
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
        β n v w e0 e0 m =
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
        β n v w e0 m := rfl

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_selectedEdge_eq
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
        w e0 e0 m =
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m := by
  simp [doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge,
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand,
    doubledBoxResidualMomentEmptyBranchSummand]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_selectedEdge_eq
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge β n
        v w e0 e0 m =
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m := by
  simp [doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge,
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand,
    doubledBoxResidualMomentInnerPairBranchSummand]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_edge_ne_eq_unincrementedMultiplicity
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hne : ew ≠ e0) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
        w e0 ew m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        (β *
          (((m ew : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) := by
  simp [doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge,
    Function.update_of_ne hne]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_edge_ne_eq_unincrementedMultiplicity
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hne : ew ≠ e0) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        (β *
          (((m ew : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m)) := by
  simp [doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge,
    Function.update_of_ne hne]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_edge_ne_eq_sourceSector_card_mul_unincrementedMultiplicity
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hne : ew ≠ e0) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge β
        n v w e0 ew m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card * m ew : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  dsimp [doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge]
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairs_update_ne_card_eq_sourceSector_card_mul
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v) (m := m) hne]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_edge_ne_eq_sourceSector_card_mul_unincrementedMultiplicity
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hne : ew ≠ e0) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
        β n v w e0 ew m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card * m ew : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge]
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairs_update_ne_card_eq_sourceSector_card_mul
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v) (m := m) hne]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_eq_beta_mul_selectedCopyPairDomainAtEdge
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
        w e0 ew m =
      β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) ew).card : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  dsimp [doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge]
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairs_card
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := Function.update m e0 (m e0 + 1)) (e0 := ew)]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_eq_beta_mul_selectedCopyPairDomainAtEdge
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m =
      β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) ew).card : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m := by
  dsimp [
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge]
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairs_card
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := Function.update m e0 (m e0 + 1)) (e0 := ew)]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_eq_selectedCopyPairDomainAtEdge_sum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
        w e0 ew m =
      ∑ _p ∈
        edgeCopySourceSectorSelectedEdgeCopyPairs (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) ew,
        β *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_eq_beta_mul_selectedCopyPairDomainAtEdge]
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairs_const_sum_eq_card_mul
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := Function.update m e0 (m e0 + 1)) (e0 := ew)]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_eq_selectedCopyPairDomainAtEdge_sum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m =
      ∑ _p ∈
        edgeCopySourceSectorSelectedEdgeCopyPairs (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) ew,
        β *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_eq_beta_mul_selectedCopyPairDomainAtEdge]
  rw [
    edgeCopySourceSectorSelectedEdgeCopyPairs_const_sum_eq_card_mul
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := Function.update m e0 (m e0 + 1)) (e0 := ew)]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_le_of_selectedCopyPairDomainAtEdge_sum_le
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (budget : ℝ)
    (hbudget :
      (∑ _p ∈
        edgeCopySourceSectorSelectedEdgeCopyPairs (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) ew,
        β *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤ budget) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
        w e0 ew m ≤ budget := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_eq_selectedCopyPairDomainAtEdge_sum]
  exact hbudget

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_le_of_selectedCopyPairDomainAtEdge_sum_le
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (budget : ℝ)
    (hbudget :
      (∑ _p ∈
        edgeCopySourceSectorSelectedEdgeCopyPairs (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) ew,
        β *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) ≤ budget) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m ≤ budget := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_eq_selectedCopyPairDomainAtEdge_sum]
  exact hbudget

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_eq_zero_of_edge_ne_multiplicity_eq_zero
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hne : ew ≠ e0) (hmew : m ew = 0) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
        w e0 ew m = 0 := by
  simp [doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge,
    Function.update_of_ne hne, hmew]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_eq_zero_of_edge_ne_multiplicity_eq_zero
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hne : ew ≠ e0) (hmew : m ew = 0) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m = 0 := by
  simp [doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge,
    Function.update_of_ne hne, hmew]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_filter_multiplicity_eq_zero_sum_eq_zero
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hne : ew ≠ e0) :
    (∑ m ∈ Ω.filter (fun m => m ew = 0),
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v w e0 ew m) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_eq_zero_of_edge_ne_multiplicity_eq_zero
      β n v w m hne (Finset.mem_filter.mp hm).2

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_filter_multiplicity_eq_zero_sum_eq_zero
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hne : ew ≠ e0) :
    (∑ m ∈ Ω.filter (fun m => m ew = 0),
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_eq_zero_of_edge_ne_multiplicity_eq_zero
      β n v w m hne (Finset.mem_filter.mp hm).2

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_sum_eq_filter_multiplicity_ne_zero_sum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hne : ew ≠ e0) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v w e0 ew m) =
      ∑ m ∈ Ω.filter (fun m => m ew ≠ 0),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v w e0 ew m := by
  classical
  let F :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v w e0 ew m
  let P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    fun m => m ew ≠ 0
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Ω) (p := P)
    (f := F)
  have hnot_zero :
      (∑ m ∈ Ω.filter (fun m => ¬ P m), F m) = 0 := by
    have hfilter :
        Ω.filter (fun m => ¬ P m) = Ω.filter (fun m => m ew = 0) := by
      ext m
      by_cases hmew : m ew = 0
      · simp [P, hmew]
      · simp [P, hmew]
    rw [hfilter]
    simpa [F] using
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_filter_multiplicity_eq_zero_sum_eq_zero
        β n v w Ω hne
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v w e0 ew m) =
        (∑ m ∈ Ω.filter P, F m) +
          ∑ m ∈ Ω.filter (fun m => ¬ P m), F m := by
        simpa [F, P] using hsplit.symm
    _ = ∑ m ∈ Ω.filter P, F m := by rw [hnot_zero, add_zero]
    _ =
      ∑ m ∈ Ω.filter (fun m => m ew ≠ 0),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v w e0 ew m := by
        rfl

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_sum_eq_filter_multiplicity_ne_zero_sum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hne : ew ≠ e0) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m) =
      ∑ m ∈ Ω.filter (fun m => m ew ≠ 0),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v w e0 ew m := by
  classical
  let F :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m
  let P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    fun m => m ew ≠ 0
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Ω) (p := P)
    (f := F)
  have hnot_zero :
      (∑ m ∈ Ω.filter (fun m => ¬ P m), F m) = 0 := by
    have hfilter :
        Ω.filter (fun m => ¬ P m) = Ω.filter (fun m => m ew = 0) := by
      ext m
      by_cases hmew : m ew = 0
      · simp [P, hmew]
      · simp [P, hmew]
    rw [hfilter]
    simpa [F] using
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_filter_multiplicity_eq_zero_sum_eq_zero
        β n v w Ω hne
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m) =
        (∑ m ∈ Ω.filter P, F m) +
          ∑ m ∈ Ω.filter (fun m => ¬ P m), F m := by
        simpa [F, P] using hsplit.symm
    _ = ∑ m ∈ Ω.filter P, F m := by rw [hnot_zero, add_zero]
    _ =
      ∑ m ∈ Ω.filter (fun m => m ew ≠ 0),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v w e0 ew m := by
        rfl

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v w e0 ew m := by
  dsimp [doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge]
  exact
    mul_nonneg (by positivity)
      (mul_nonneg hβ
        (mul_nonneg (by positivity)
          (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
            (by intro e; norm_num))))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m := by
  dsimp [
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge]
  exact
    mul_nonneg (by positivity)
      (mul_nonneg hβ
        (mul_nonneg (by positivity)
          (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m hβ
            (by intro e; norm_num))))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v w e0 ew m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_nonneg
        hβ e0 ew m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_nonneg
        hβ e0 ew m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_owner_incrementInserted_add_outsideCurrentAtEdge_budget_of_update_zero_ownerEdge_eq
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0)
    (owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew)
    (ownerBudget outsideBudget : ℝ)
    (hownerBudget :
      β *
          (((edgeCopySourceSectorContainingBothCopies
            (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :
              ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
        ownerBudget)
    (houtsideBudget :
      β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m ≤
        outsideBudget) :
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m ≤
      ownerBudget + outsideBudget := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  have hbase : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  simpa [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand,
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge,
    G, A, base] using
    beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_budget_of_update_zero_ownerEdge_eq
      G A m e0 ew hmzero owner hownerEdge β base ownerBudget outsideBudget
      hβ hbase hownerBudget (by
        simpa [
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge,
          G, A, base] using houtsideBudget)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_owner_incrementInserted_add_outsideCurrentAtEdge_budget_of_update_zero_ownerEdge_eq
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0)
    (owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew)
    (ownerBudget outsideBudget : ℝ)
    (hownerBudget :
      β *
          (((edgeCopySourceSectorContainingBothCopies
            (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :
              ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) ≤
        ownerBudget)
    (houtsideBudget :
      β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m ≤
        outsideBudget) :
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
      ownerBudget + outsideBudget := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hbase : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  simpa [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand,
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge,
    G, A, base] using
    beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_outsideCurrent_budget_of_update_zero_ownerEdge_eq
      G A m e0 ew hmzero owner hownerEdge β base ownerBudget outsideBudget
      hβ hbase hownerBudget (by
        simpa [
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge,
          G, A, base] using houtsideBudget)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_budget_of_update_zero_ownerEdge_eq
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0)
    (owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0)
    (ownerBudget outsideBudget : ℝ)
    (hownerBudget :
      β *
          (((edgeCopySourceSectorContainingBothCopies
            (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :
              ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
        ownerBudget)
    (houtsideBudget :
      β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m ≤
        outsideBudget) :
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m ≤
      ownerBudget + outsideBudget := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  have hbase : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  simpa [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand,
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand,
    G, A, base] using
    beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_budget_of_update_zero_ownerEdge_eq
      G A m e0 hmzero owner hownerEdge β base ownerBudget outsideBudget hβ
      hbase hownerBudget (by
        simpa [
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand,
          G, A, base] using houtsideBudget)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_budget_of_update_zero_ownerEdge_eq
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0)
    (owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = e0)
    (ownerBudget outsideBudget : ℝ)
    (hownerBudget :
      β *
          (((edgeCopySourceSectorContainingBothCopies
            (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) owner
            (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :
              ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) ≤
        ownerBudget)
    (houtsideBudget :
      β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m ≤
        outsideBudget) :
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
      ownerBudget + outsideBudget := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hbase : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  simpa [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand,
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand,
    G, A, base] using
    beta_mul_edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_mul_le_owner_incrementInserted_add_selectedEdgeOutsideCurrent_budget_of_update_zero_ownerEdge_eq
      G A m e0 hmzero owner hownerEdge β base ownerBudget outsideBudget hβ
      hbase hownerBudget (by
        simpa [
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand,
          G, A, base] using houtsideBudget)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m =
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β
          n v w e0 m +
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hcard :
      ((edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0).card : ℝ) =
        ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0).card :
          ℝ) +
          ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0).card :
            ℝ) := by
    have h :=
      edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
        G A M e0
    rw [← h]
    norm_num [Nat.cast_add]
  dsimp [doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand,
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand,
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand]
  rw [show
      ((edgeCopySourceSectorSelectedEdgeCopyPairs (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) =
        ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) +
          ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card : ℝ) by
        simpa [G, A, M] using hcard]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m =
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m +
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hcard :
      ((edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0).card : ℝ) =
        ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0).card :
          ℝ) +
          ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0).card :
            ℝ) := by
    have h :=
      edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
        G A M e0
    rw [← h]
    norm_num [Nat.cast_add]
  dsimp [doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand,
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand,
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand]
  rw [show
      ((edgeCopySourceSectorSelectedEdgeCopyPairs (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card : ℝ) =
        ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) +
          ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card : ℝ) by
        simpa [G, A, M] using hcard]
  ring

set_option linter.style.longLine false in


theorem selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
    {β W X : ℝ} (hβ : 0 < β)
    (hX : β * X ≤ ((β / 6) * W) / 768) :
    X ≤ (W / 6) / 768 := by
  have hscaled : β * X ≤ β * ((W / 6) / 768) := by
    calc
      β * X ≤ ((β / 6) * W) / 768 := hX
      _ = β * ((W / 6) / 768) := by ring
  exact le_of_mul_le_mul_left hscaled hβ

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_le_weight_div_six_div_768
    {β W : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hin :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
          v w e0 m ≤
        (W / 6) / 768)
    (hout :
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m ≤
        (W / 6) / 768) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m ≤
      (W / 6) / 384 := by
  calc
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m =
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β
            n v w e0 m +
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m := by
          rw [
            doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent]
    _ ≤ (W / 6) / 768 + (W / 6) / 768 := add_le_add hin hout
    _ = (W / 6) / 384 := by ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_le_weight_div_six_div_384_of_beta_mul_inCurrent_outsideCurrent_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hin :
      β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m ≤
        ((β / 6) * W) / 768)
    (hout :
      β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m ≤
        ((β / 6) * W) / 768) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m ≤
      (W / 6) / 384 := by
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_le_weight_div_six_div_768
      (β := β) (W := W) (n := n) (v := v) (w := w) e0 m
      (selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
        (β := β) (W := W)
        (X :=
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m)
        hβ hin)
      (selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
        (β := β) (W := W)
        (X :=
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m)
        hβ hout)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_le_weight_div_six_div_768
    {β W : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hin :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
        (W / 6) / 768)
    (hout :
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
        (W / 6) / 768) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
        w e0 m ≤
      (W / 6) / 384 := by
  calc
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
        w e0 m =
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m +
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m := by
          rw [
            doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent]
    _ ≤ (W / 6) / 768 + (W / 6) / 768 := add_le_add hin hout
    _ = (W / 6) / 384 := by ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_le_weight_div_six_div_384_of_beta_mul_inCurrent_outsideCurrent_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hin :
      β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m ≤
        ((β / 6) * W) / 768)
    (hout :
      β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m ≤
        ((β / 6) * W) / 768) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
        w e0 m ≤
      (W / 6) / 384 := by
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_le_weight_div_six_div_768
      (β := β) (W := W) (n := n) (v := v) (w := w) e0 m
      (selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
        (β := β) (W := W)
        (X :=
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m)
        hβ hin)
      (selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
        (β := β) (W := W)
        (X :=
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m)
        hβ hout)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m := by
  dsimp [doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m := by
  dsimp [doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge β
        n v w e0 ew m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
        β n v w e0 ew m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
        v w e0 m := by
  dsimp [doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v w e0 m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
        β n v w e0 ew m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
        β n v w e0 ew m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β
        n v w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
        β n v w e0 ew m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_nonneg
        hβ e0 ew m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
        β n v w e0 ew m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_nonneg
        hβ e0 ew m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_totalPairCardAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
        β n v w e0 ew m ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge β
        n v w e0 ew m := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hsubset :
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M ew ⊆
        edgeCopySourceSectorSelectedEdgeCopyPairs G A M ew := by
    intro p hp
    exact
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem G A M ew
        p).mp hp).1
  have hcard :
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M ew).card :
          ℝ) ≤
        ((edgeCopySourceSectorSelectedEdgeCopyPairs G A M ew).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hbase_nonneg :
      0 ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  dsimp [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge,
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge]
  exact
    mul_le_mul_of_nonneg_right (by simpa [G, A, M] using hcard)
      hbase_nonneg

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_totalPairCardAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
        β n v w e0 ew m ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
        β n v w e0 ew m := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hsubset :
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M ew ⊆
        edgeCopySourceSectorSelectedEdgeCopyPairs G A M ew := by
    intro p hp
    exact
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem G A M ew
        p).mp hp).1
  have hcard :
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M ew).card :
          ℝ) ≤
        ((edgeCopySourceSectorSelectedEdgeCopyPairs G A M ew).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hbase_nonneg :
      0 ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  dsimp [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge,
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge]
  exact
    mul_le_mul_of_nonneg_right (by simpa [G, A, M] using hcard)
      hbase_nonneg

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_totalPairCardAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m ≤
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m := by
  exact
    mul_le_mul_of_nonneg_left
      (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_totalPairCardAtEdge
        hβ e0 ew m)
      hβ

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_totalPairCardAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m ≤
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m := by
  exact
    mul_le_mul_of_nonneg_left
      (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_totalPairCardAtEdge
        hβ e0 ew m)
      hβ

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_finset_sum_le_totalPairCardAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m) ≤
      ∑ m ∈ Ω,
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_totalPairCardAtEdge
        hβ e0 ew m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_finset_sum_le_totalPairCardAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m) ≤
      ∑ m ∈ Ω,
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_totalPairCardAtEdge
        hβ e0 ew m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_edge_sum_le_totalPairCardAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ S,
      ∑ m ∈ Ω ew,
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m) ≤
      ∑ ew ∈ S,
        ∑ m ∈ Ω ew,
          β *
            doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
              β n v w e0 ew m := by
  exact
    Finset.sum_le_sum (fun ew _hew =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_finset_sum_le_totalPairCardAtEdge
        hβ e0 ew (Ω ew))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_edge_sum_le_totalPairCardAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ S,
      ∑ m ∈ Ω ew,
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m) ≤
      ∑ ew ∈ S,
        ∑ m ∈ Ω ew,
          β *
            doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
              β n v w e0 ew m := by
  exact
    Finset.sum_le_sum (fun ew _hew =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_finset_sum_le_totalPairCardAtEdge
        hβ e0 ew (Ω ew))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentEdges_sum_le_totalPairCardAtEdge_budget
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (totalBudget : ℝ)
    (htotalBudget :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          β *
            doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
              β n v w e0 ew m) ≤ totalBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m) ≤ totalBudget := by
  exact
    (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_edge_sum_le_totalPairCardAtEdge
      (β := β) hβ (n := n) (v := v) (w := w) e0
      (doubledBoxOriginIncidentEdges n)
      (fun ew =>
        (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew))).trans
      htotalBudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentEdges_sum_le_totalPairCardAtEdge_budget
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (totalBudget : ℝ)
    (htotalBudget :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          β *
            doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
              β n v w e0 ew m) ≤ totalBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m) ≤ totalBudget := by
  exact
    (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_edge_sum_le_totalPairCardAtEdge
      (β := β) hβ (n := n) (v := v) (w := w) e0
      (doubledBoxOriginIncidentEdges n)
      (fun ew =>
        (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew))).trans
      htotalBudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_eq_switchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m =
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v w e0 ew m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge,
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge]
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs_card]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_eq_switchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m =
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m := by
  dsimp [
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge,
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge]
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs_card]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_finset_sum_eq_switchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m) =
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v w e0 ew m := by
  refine Finset.sum_congr rfl ?_
  intro m _hm
  rw [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_eq_switchedSourceSectorResidualMomentEmptyBranchSummandAtEdge]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_finset_sum_eq_switchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m) =
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v w e0 ew m := by
  refine Finset.sum_congr rfl ?_
  intro m _hm
  rw [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_eq_switchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_edge_sum_eq_switchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ S,
      ∑ m ∈ Ω ew,
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m) =
      ∑ ew ∈ S,
        ∑ m ∈ Ω ew,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v w e0 ew m := by
  refine Finset.sum_congr rfl ?_
  intro ew _hew
  rw [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_finset_sum_eq_switchedSourceSectorResidualMomentEmptyBranchSummandAtEdge]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_edge_sum_eq_switchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ S,
      ∑ m ∈ Ω ew,
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m) =
      ∑ ew ∈ S,
        ∑ m ∈ Ω ew,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v w e0 ew m := by
  refine Finset.sum_congr rfl ?_
  intro ew _hew
  rw [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_finset_sum_eq_switchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_switchedSourceSectorResidualMomentAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m ≤
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v w e0 ew m := by
  calc
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m ≤
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m :=
          beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_totalPairCardAtEdge
            hβ e0 ew m
    _ =
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
          v w e0 ew m :=
          beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_eq_switchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v w e0 ew m

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_switchedSourceSectorResidualMomentAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m ≤
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m := by
  calc
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m ≤
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m :=
          beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_totalPairCardAtEdge
            hβ e0 ew m
    _ =
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v w e0 ew m :=
          beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_eq_switchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v w e0 ew m

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_finset_sum_le_switchedSourceSectorResidualMomentAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v w e0 ew m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v w e0 ew m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_switchedSourceSectorResidualMomentAtEdge
        hβ e0 ew m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_finset_sum_le_switchedSourceSectorResidualMomentAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v w e0 ew m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v w e0 ew m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_switchedSourceSectorResidualMomentAtEdge
        hβ e0 ew m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_edge_sum_le_switchedSourceSectorResidualMomentAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ S,
      ∑ m ∈ Ω ew,
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m) ≤
      ∑ ew ∈ S,
        ∑ m ∈ Ω ew,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v w e0 ew m := by
  exact
    Finset.sum_le_sum (fun ew _hew =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_finset_sum_le_switchedSourceSectorResidualMomentAtEdge
        hβ e0 ew (Ω ew))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_edge_sum_le_switchedSourceSectorResidualMomentAtEdge
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ S,
      ∑ m ∈ Ω ew,
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m) ≤
      ∑ ew ∈ S,
        ∑ m ∈ Ω ew,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v w e0 ew m := by
  exact
    Finset.sum_le_sum (fun ew _hew =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_finset_sum_le_switchedSourceSectorResidualMomentAtEdge
        hβ e0 ew (Ω ew))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentEdges_sum_le_switchedSourceSectorResidualMomentAtEdge_budget
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (residualBudget : ℝ)
    (hresidualBudget :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v w e0 ew m) ≤ residualBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m) ≤ residualBudget := by
  exact
    (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_edge_sum_le_switchedSourceSectorResidualMomentAtEdge
      hβ e0 (doubledBoxOriginIncidentEdges n)
      (fun ew =>
        (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew))).trans
      hresidualBudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentEdges_sum_le_switchedSourceSectorResidualMomentAtEdge_budget
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (residualBudget : ℝ)
    (hresidualBudget :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v w e0 ew m) ≤ residualBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m) ≤ residualBudget := by
  exact
    (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_edge_sum_le_switchedSourceSectorResidualMomentAtEdge
      hβ e0 (doubledBoxOriginIncidentEdges n)
      (fun ew =>
        (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew))).trans
      hresidualBudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_originIncidentEdges_sum_le_switchedSourceSectorResidualMomentAtEdge_budget
    {β : ℝ} {n : ℕ} (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (residualBudget : ℝ)
    (hresidualBudget :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v w e0 ew m) ≤ residualBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m) ≤ residualBudget := by
  rw [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummandAtEdge_edge_sum_eq_switchedSourceSectorResidualMomentEmptyBranchSummandAtEdge]
  exact hresidualBudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_originIncidentEdges_sum_le_switchedSourceSectorResidualMomentAtEdge_budget
    {β : ℝ} {n : ℕ} (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (residualBudget : ℝ)
    (hresidualBudget :
      (∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v w e0 ew m) ≤ residualBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m) ≤ residualBudget := by
  rw [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummandAtEdge_edge_sum_eq_switchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge]
  exact hresidualBudget

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_eq_inCurrent_add_outsideCurrent
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m) =
      (∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m) +
        ∑ m ∈ Ω,
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m := by
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m) =
        ∑ m ∈ Ω,
          (doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
              β n v w e0 m +
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v w e0 m) := by
          refine Finset.sum_congr rfl ?_
          intro m _hm
          rw [
            doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent]
    _ =
      (∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m) +
        ∑ m ∈ Ω,
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m := by
      rw [Finset.sum_add_distrib]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_eq_inCurrent_add_outsideCurrent
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
        n v w e0 m) =
      (∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) +
        ∑ m ∈ Ω,
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m := by
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
        n v w e0 m) =
        ∑ m ∈ Ω,
          (doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m +
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m) := by
          refine Finset.sum_congr rfl ?_
          intro m _hm
          rw [
            doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent]
    _ =
      (∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) +
        ∑ m ∈ Ω,
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m := by
      rw [Finset.sum_add_distrib]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_totalPairCardEmptySourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n v
        w e0 m ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m := by
  have hsplit :=
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent
      β n v w e0 m
  have hout :
      0 ≤
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
      hβ e0 m
  linarith

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_totalPairCardInnerPairSourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
        n v w e0 m := by
  have hsplit :=
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent
      β n v w e0 m
  have hout :
      0 ≤
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
      hβ e0 m
  linarith

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_totalPairCardEmptySourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v w e0 m ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m := by
  have hsplit :=
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent
      β n v w e0 m
  have hin :
      0 ≤
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
      hβ e0 m
  linarith

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_totalPairCardInnerPairSourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m ≤
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
        n v w e0 m := by
  have hsplit :=
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent
      β n v w e0 m
  have hin :
      0 ≤
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
      hβ e0 m
  linarith

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_finset_sum_le_totalPairCardEmptySourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
        v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v w e0 m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_totalPairCardEmptySourcePairSummand
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_totalPairCardInnerPairSourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
          n v w e0 m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_totalPairCardInnerPairSourcePairSummand
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_finset_sum_le_totalPairCardEmptySourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v w e0 m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_totalPairCardEmptySourcePairSummand
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_totalPairCardInnerPairSourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
          n v w e0 m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_totalPairCardInnerPairSourcePairSummand
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_base_le_of_inCurrent_nonempty
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hin :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).Nonempty) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≤
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
        β n v w e0 m := by
  classical
  let S :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  have hcard_one_nat : 1 ≤ S.card := by
    have hpos : 0 < S.card := by
      simpa [S] using Finset.Nonempty.card_pos hin
    omega
  have hcard_one : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard_one_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  calc
    base = (1 : ℝ) * base := by ring
    _ ≤ (S.card : ℝ) * base :=
      mul_le_mul_of_nonneg_right hcard_one hbase_nonneg
    _ =
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m := by
      simp [
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand,
        S, base]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_base_le_of_inCurrent_nonempty
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hin :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).Nonempty) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m ≤
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m := by
  classical
  let S :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hcard_one_nat : 1 ≤ S.card := by
    have hpos : 0 < S.card := by
      simpa [S] using Finset.Nonempty.card_pos hin
    omega
  have hcard_one : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard_one_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  calc
    base = (1 : ℝ) * base := by ring
    _ ≤ (S.card : ℝ) * base :=
      mul_le_mul_of_nonneg_right hcard_one hbase_nonneg
    _ =
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m := by
      simp [
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand,
        S, base]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_base_le_of_residualContaining_update_zero
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0)
    (hres :
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty)) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≤
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
        β n v w e0 m := by
  have hin :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).Nonempty :=
    ((doubledBoxOriginToInnerEndpoint_residualContaining_nonempty_iff_predecessorSourceSector_not_nonempty_and_selectedEdgeCopyPairsInCurrent_nonempty_update_zero
      (n := n) (v := v) (w := w) (e0 := e0) (m := m) hmzero).mp hres).2
  exact
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_base_le_of_inCurrent_nonempty
      hβ hin

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_base_le_of_residualContaining_update_zero
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hmzero : m e0 = 0)
    (hres :
      ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorContainingCopy
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty)) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m ≤
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m := by
  have hin :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).Nonempty :=
    ((doubledBoxOriginToInnerEndpoint_residualContaining_nonempty_iff_predecessorSourceSector_not_nonempty_and_selectedEdgeCopyPairsInCurrent_nonempty_update_zero
      (n := n) (v := v) (w := w) (e0 := e0) (m := m) hmzero).mp hres).2
  exact
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_base_le_of_inCurrent_nonempty
      hβ hin

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_nonneg
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_nonneg
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_copies
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        IsingFK.boxOrigin 3 (2 * n) ∉
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m =
      0 := by
  have horigin_left_v :
      IsingFK.boxOrigin 3 (2 * n) ∈
        doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simp
  have hleft :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_v habsent
  simp [doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand,
    hleft]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m =
      0 :=
  doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_copies
    β e0 m hov
    (fluxEdgeCopy_endsM_not_mem_of_edge_support_absent
      (FK.boxGraph 3 (2 * n)) habsent)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_copies
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        IsingFK.boxOrigin 3 (2 * n) ∉
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m =
      0 := by
  have horigin_left_w :
      IsingFK.boxOrigin 3 (2 * n) ∈
        doubledBoxOriginToInnerEndpointSource n w := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair how]
    simp
  have hright :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_w habsent
  simp [doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand,
    hright]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m =
      0 :=
  doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_copies
    β e0 m how
    (fluxEdgeCopy_endsM_not_mem_of_edge_support_absent
      (FK.boxGraph 3 (2 * n)) habsent)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m =
      0 :=
  doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    β e0 m hov
    (doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
      hnot)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m =
      0 :=
  doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    β e0 m how
    (doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
      hnot)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
        v w e0 m =
      0 := by
  have htotal :
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
          w e0 m =
        0 :=
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov hnot
  have hsum :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
          v w e0 m +
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m =
        0 := by
    simpa [
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent
        β n v w e0 m] using htotal
  have hin_nonneg :
      0 ≤
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
      hβ e0 m
  have hout_nonneg :
      0 ≤
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
      hβ e0 m
  exact le_antisymm
    (by
      calc
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m ≤
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
              β n v w e0 m +
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v w e0 m := by
            exact le_add_of_nonneg_right hout_nonneg
        _ = 0 := hsum)
    hin_nonneg

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v w e0 m =
      0 := by
  have htotal :
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
          w e0 m =
        0 :=
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov hnot
  have hsum :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
          v w e0 m +
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m =
        0 := by
    simpa [
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent
        β n v w e0 m] using htotal
  have hin_nonneg :
      0 ≤
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
      hβ e0 m
  have hout_nonneg :
      0 ≤
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
      hβ e0 m
  exact le_antisymm
    (by
      calc
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m ≤
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
              β n v w e0 m +
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v w e0 m := by
            simpa [zero_add] using
              add_le_add_right hin_nonneg
                (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m)
        _ = 0 := hsum)
    hout_nonneg

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m =
      0 := by
  have htotal :
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
          v w e0 m =
        0 :=
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m how hnot
  have hsum :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m +
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m =
        0 := by
    simpa [
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent
        β n v w e0 m] using htotal
  have hin_nonneg :
      0 ≤
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
      hβ e0 m
  have hout_nonneg :
      0 ≤
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
      hβ e0 m
  exact le_antisymm
    (by
      calc
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m ≤
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m +
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m := by
            exact le_add_of_nonneg_right hout_nonneg
        _ = 0 := hsum)
    hin_nonneg

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m =
      0 := by
  have htotal :
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
          v w e0 m =
        0 :=
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m how hnot
  have hsum :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m +
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m =
        0 := by
    simpa [
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent
        β n v w e0 m] using htotal
  have hin_nonneg :
      0 ≤
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
      hβ e0 m
  have hout_nonneg :
      0 ≤
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
      hβ e0 m
  exact le_antisymm
    (by
      calc
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m ≤
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m +
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m := by
            simpa [zero_add] using
              add_le_add_right hin_nonneg
                (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m)
        _ = 0 := hsum)
    hout_nonneg

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov hnot

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
        β n v w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m how hnot

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
        v w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      hβ e0 m hov hnot

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      hβ e0 m hov hnot

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      hβ e0 m how hnot

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      hβ e0 m how hnot

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ m ∈ Ω,
        ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
          m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m hov (habsent m hm)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ m ∈ Ω,
        ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
          m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
        β n v w e0 m) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m how (habsent m hm)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
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
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
      e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  let o := IsingFK.boxOrigin 3 (2 * n)
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k
  have horigin_not_mem_e0 : o ∉ e0.1 := by
    rw [hedge]
    simp [Sym2.mem_iff, o, hov, how]
  have habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → o ∉ e.1 := by
    intro e hme
    by_cases he : e = e0
    · simpa [he, o] using horigin_not_mem_e0
    · have hzero : m e = 0 := by
        simp [m, he]
      exact False.elim (hme hzero)
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m hov (by simpa [o] using habsent)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
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
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
      v w e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  let o := IsingFK.boxOrigin 3 (2 * n)
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k
  have horigin_not_mem_e0 : o ∉ e0.1 := by
    rw [hedge]
    simp [Sym2.mem_iff, o, hov, how]
  have habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → o ∉ e.1 := by
    intro e hme
    by_cases he : e = e0
    · simpa [he, o] using horigin_not_mem_e0
    · have hzero : m e = 0 := by
        simp [m, he]
      exact False.elim (hme hzero)
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m how (by simpa [o] using habsent)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
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
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
      v w e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k
  have hbranch :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
        v w e0 m = 0 := by
    have htotal :
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
            w e0 m =
          0 := by
      simpa [m] using
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
          β e0 k hedge hov how
    have hsum :
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
            v w e0 m +
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m =
          0 := by
      simpa [
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent
          β n v w e0 m] using htotal
    have hin_nonneg :
        0 ≤
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m :=
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
        hβ e0 m
    have hout_nonneg :
        0 ≤
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m :=
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
        hβ e0 m
    exact le_antisymm
      (by
        calc
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
              β n v w e0 m ≤
            doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                β n v w e0 m +
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                β n v w e0 m := by
              exact le_add_of_nonneg_right hout_nonneg
          _ = 0 := hsum)
      hin_nonneg
  simpa [m] using hbranch

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
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
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand β
      n v w e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k
  have hbranch :
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v w e0 m = 0 := by
    have htotal :
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
            w e0 m =
          0 := by
      simpa [m] using
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
          β e0 k hedge hov how
    have hsum :
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β n
            v w e0 m +
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m =
          0 := by
      simpa [
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent
          β n v w e0 m] using htotal
    have hin_nonneg :
        0 ≤
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m :=
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
        hβ e0 m
    have hout_nonneg :
        0 ≤
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m :=
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
        hβ e0 m
    exact le_antisymm
      (by
        calc
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v w e0 m ≤
            doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                β n v w e0 m +
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                β n v w e0 m := by
              simpa [zero_add] using
                add_le_add_right hin_nonneg
                  (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                    β n v w e0 m)
          _ = 0 := hsum)
      hout_nonneg
  simpa [m] using hbranch

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
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
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
      β n v w e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k
  have hbranch :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m = 0 := by
    have htotal :
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
            v w e0 m =
          0 := by
      simpa [m] using
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
          β e0 k hedge hov how
    have hsum :
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m +
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m =
          0 := by
      simpa [
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent
          β n v w e0 m] using htotal
    have hin_nonneg :
        0 ≤
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m :=
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
        hβ e0 m
    have hout_nonneg :
        0 ≤
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m :=
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
        hβ e0 m
    exact le_antisymm
      (by
        calc
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m ≤
            doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                β n v w e0 m +
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                β n v w e0 m := by
              exact le_add_of_nonneg_right hout_nonneg
          _ = 0 := hsum)
      hin_nonneg
  simpa [m] using hbranch

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
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
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
      β n v w e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k
  have hbranch :
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v w e0 m = 0 := by
    have htotal :
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
            v w e0 m =
          0 := by
      simpa [m] using
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
          β e0 k hedge hov how
    have hsum :
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m +
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m =
          0 := by
      simpa [
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent
          β n v w e0 m] using htotal
    have hin_nonneg :
        0 ≤
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m :=
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
        hβ e0 m
    have hout_nonneg :
        0 ≤
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m :=
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
        hβ e0 m
    exact le_antisymm
      (by
        calc
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m ≤
            doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                β n v w e0 m +
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                β n v w e0 m := by
              simpa [zero_add] using
                add_le_add_right hin_nonneg
                  (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                    β n v w e0 m)
          _ = 0 := hsum)
      hout_nonneg
  simpa [m] using hbranch

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_selectedEdgeCopies_le_zero
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
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β
          n v w e0
          (Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) ≤
      0 := by
  rw [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
      hβ e0 k hedge hov how,
    mul_zero]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_selectedEdgeCopies_le_zero
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
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0
          (Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) ≤
      0 := by
  rw [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
      hβ e0 k hedge hov how,
    mul_zero]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_selectedEdgeCopies_le_zero
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
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0
          (Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) ≤
      0 := by
  rw [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
      hβ e0 k hedge hov how,
    mul_zero]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_selectedEdgeCopies_le_zero
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
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0
          (Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) ≤
      0 := by
  rw [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
      hβ e0 k hedge hov how,
    mul_zero]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_singleton_selectedEdgeCopies_sum_eq_zero
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
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β
          n v w e0 m) =
      0 := by
  simp [doubledBoxSelectedEdgeCopiesSingletonCutoff,
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
      hβ e0 k hedge hov how]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_singleton_selectedEdgeCopies_sum_eq_zero
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
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m) =
      0 := by
  simp [doubledBoxSelectedEdgeCopiesSingletonCutoff,
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
      hβ e0 k hedge hov how]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_singleton_selectedEdgeCopies_sum_eq_zero
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
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) =
      0 := by
  simp [doubledBoxSelectedEdgeCopiesSingletonCutoff,
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
      hβ e0 k hedge hov how]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_singleton_selectedEdgeCopies_sum_eq_zero
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
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) =
      0 := by
  simp [doubledBoxSelectedEdgeCopiesSingletonCutoff,
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
      hβ e0 k hedge hov how]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSector_card_mul_succ
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card * (m e0 + 1) : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  dsimp [doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand]
  rw [doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sourceSector_card_mul_succ]

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSector_card_mul_succ
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card * (m e0 + 1) : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
  dsimp [doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand]
  rw [doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sourceSector_card_mul_succ]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_switchedSourceSectorResidualMomentEmptyBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v w e0 m =
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m := by
  rw [doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSector_card_mul_succ]
  dsimp [doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand,
    doubledBoxResidualMomentEmptyBranchSummand]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_switchedSourceSectorResidualMomentInnerPairBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
          β n v w e0 m =
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m := by
  rw [doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSector_card_mul_succ]
  dsimp [doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand,
    doubledBoxResidualMomentInnerPairBranchSummand]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in

theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_switchedTotalPairCardEmptySourcePairSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m =
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v w e0 m :=
  (beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_switchedSourceSectorResidualMomentEmptyBranchSummand
    β n v w e0 m).symm

set_option linter.style.longLine false in

theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_switchedTotalPairCardInnerPairSourcePairSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m =
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
          β n v w e0 m :=
  (beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_switchedSourceSectorResidualMomentInnerPairBranchSummand
    β n v w e0 m).symm

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_384_of_totalPairCardEmpty_le_weight_div_six_div_384
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hcard :
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
          w e0 m ≤
        (W / 6) / 384) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m ≤
      ((β / 6) * W) / 384 := by
  calc
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m =
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β
            n v w e0 m := by
          rw [
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_switchedTotalPairCardEmptySourcePairSummand]
    _ ≤ β * ((W / 6) / 384) := by
      exact mul_le_mul_of_nonneg_left hcard hβ
    _ = ((β / 6) * W) / 384 := by ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_384_of_totalPairCardInner_le_weight_div_six_div_384
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hcard :
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
          n v w e0 m ≤
        (W / 6) / 384) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m ≤
      ((β / 6) * W) / 384 := by
  calc
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m =
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v w e0 m := by
          rw [
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_switchedTotalPairCardInnerPairSourcePairSummand]
    _ ≤ β * ((W / 6) / 384) := by
      exact mul_le_mul_of_nonneg_left hcard hβ
    _ = ((β / 6) * W) / 384 := by ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_coarse_le_two_mul_four_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m ≤
      2 *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  rw [
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSector_card_mul_succ,
    Nat.cast_mul]
  simpa [mul_assoc] using
    edgeCopySourceSector_card_update_succ_mul_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_mul_four_beta
      (FK.boxGraph 3 (2 * n)) hβ
      (doubledBoxOriginToInnerEndpointSource n v)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m e0

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_coarse_le_two_mul_four_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m ≤
      2 *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
  rw [
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSector_card_mul_succ,
    Nat.cast_mul]
  simpa [mul_assoc] using
    edgeCopySourceSector_card_update_succ_mul_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_mul_four_beta
      (FK.boxGraph 3 (2 * n)) hβ
      (doubledBoxOriginToInnerEndpointSource n v)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m e0

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_coarse_le_beta_mul_two_mul_four_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m ≤
      β *
        (2 *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_switchedTotalPairCardEmptySourcePairSummand]
  exact
    mul_le_mul_of_nonneg_left
      (doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_coarse_le_two_mul_four_beta
        hβ n v w e0 m)
      hβ

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_coarse_le_beta_mul_two_mul_four_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m ≤
      β *
        (2 *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_switchedTotalPairCardInnerPairSourcePairSummand]
  exact
    mul_le_mul_of_nonneg_left
      (doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_coarse_le_two_mul_four_beta
        hβ n v w e0 m)
      hβ

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_coarse_le_two_mul_four_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m) ≤
      ∑ m ∈ Ω,
        2 *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_coarse_le_two_mul_four_beta
        hβ n v w e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_coarse_le_two_mul_four_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
        v w e0 m) ≤
      ∑ m ∈ Ω,
        2 *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_coarse_le_two_mul_four_beta
        hβ n v w e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m ≤
      (2 * β) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  calc
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m ≤
      β *
        (2 *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) :=
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_coarse_le_beta_mul_two_mul_four_beta
        hβ n v w e0 m
    _ =
      (2 * β) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
      ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m ≤
      (2 * β) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
  calc
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m ≤
      β *
        (2 *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) :=
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_coarse_le_beta_mul_two_mul_four_beta
        hβ n v w e0 m
    _ =
      (2 * β) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
      ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummands
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0 m ≤
      (2 * β) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
  rw [doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
  calc
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m +
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m ≤
        (2 * β) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
        (2 * β) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m := by
      exact
        add_le_add
          (doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummand
            hβ n v w e0 m)
          (doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummand
            hβ n v w e0 m)
    _ =
      (2 * β) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
      ring

set_option linter.style.longLine false in

theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  have hdom :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        (2 * β) *
          edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) :=
    (edgeCopySourcePairSummand_summable G (2 * (2 * β)) (fun _ => 1) A
      (∅ : Finset (FK.boxVerts 3 (2 * n)))).mul_left (2 * β)
  refine Summable.of_nonneg_of_le ?hnonneg ?hle hdom
  · intro m
    exact
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m
  · intro m
    exact
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummand
        hβ n v w e0 m

set_option linter.style.longLine false in

theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let B := doubledBoxInnerPairSource n v w
  have hdom :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        (2 * β) *
          edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m) :=
    (edgeCopySourcePairSummand_summable G (2 * (2 * β)) (fun _ => 1) A B).mul_left
      (2 * β)
  refine Summable.of_nonneg_of_le ?hnonneg ?hle hdom
  · intro m
    exact
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m
  · intro m
    exact
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummand
        hβ n v w e0 m

set_option linter.style.longLine false in

theorem doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_summable_of_nonneg_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0
        m) := by
  have hempty :=
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
      hβ n v w e0
  have hinner :=
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
      hβ n v w e0
  simpa [doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
    using hempty.add hinner

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) ≤
      (2 * β) *
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  rw [edgeCopySourcePairSum, ← tsum_mul_left]
  exact
    (doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
      hβ n v w e0).tsum_le_tsum
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummand
          hβ n v w e0 m)
      ((edgeCopySourcePairSummand_summable G (2 * (2 * β)) (fun _ => 1) A
        (∅ : Finset (FK.boxVerts 3 (2 * n)))).mul_left (2 * β))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) ≤
      (2 * β) *
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let B := doubledBoxInnerPairSource n v w
  rw [edgeCopySourcePairSum, ← tsum_mul_left]
  exact
    (doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
      hβ n v w e0).tsum_le_tsum
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_coarse_le_two_beta_mul_four_beta_sourcePairSummand
          hβ n v w e0 m)
      ((edgeCopySourcePairSummand_summable G (2 * (2 * β)) (fun _ => 1) A B).mul_left
        (2 * β))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSums
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0
        m) ≤
      (2 * β) *
        (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) +
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) := by
  have hempty_summable :=
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
      hβ n v w e0
  have hinner_summable :=
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
      hβ n v w e0
  have hempty :=
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSum
      hβ n v w e0
  have hinner :=
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSum
      hβ n v w e0
  calc
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0
        m) =
        (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            w e0 m) +
        (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β
            n v w e0 m) := by
      conv_lhs =>
        congr
        intro m
        rw [doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
      exact Summable.tsum_add hempty_summable hinner_summable
    _ ≤
        (2 * β) *
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        (2 * β) *
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) :=
      add_le_add hempty hinner
    _ =
        (2 * β) *
          (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) +
            edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) := by
      ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) ≤
      (2 * β) *
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) ≤
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            w e0 m :=
      (doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
        hβ n v w e0).sum_le_tsum Ω
        (fun m _hm =>
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_nonneg
            (n := n) (v := v) (w := w) hβ e0 m)
    _ ≤
      (2 * β) *
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSum
        hβ n v w e0

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) ≤
      (2 * β) *
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) ≤
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β
            n v w e0 m :=
      (doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
        hβ n v w e0).sum_le_tsum Ω
        (fun m _hm =>
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_nonneg
            (n := n) (v := v) (w := w) hβ e0 m)
    _ ≤
      (2 * β) *
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSum
        hβ n v w e0

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sourcePairSums
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0
        m) ≤
      (2 * β) *
        (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) +
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) := by
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0
        m) ≤
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w
            e0 m :=
      (doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_summable_of_nonneg_beta
        hβ n v w e0).sum_le_tsum Ω
        (fun m _hm =>
          doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_nonneg
            (n := n) (v := v) (w := w) hβ e0 m)
    _ ≤
      (2 * β) *
        (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) +
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :=
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSums
        hβ n v w e0

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sharpnessSourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) ≤
      (2 * β) *
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSum
      hβ n v w e0

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sharpnessSourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) ≤
      (2 * β) *
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSum
      hβ n v w e0

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sharpnessSourcePairSums
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0
        m) ≤
      (2 * β) *
        (Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) := by
  simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
    doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_tsum_coarse_le_two_beta_mul_four_beta_sourcePairSums
      hβ n v w e0

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sharpnessSourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) ≤
      (2 * β) *
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sourcePairSum
      hβ n v w e0 Ω

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sharpnessSourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) ≤
      (2 * β) *
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sourcePairSum
      hβ n v w e0 Ω

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sharpnessSourcePairSums
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0
        m) ≤
      (2 * β) *
        (Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) := by
  simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
    doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sourcePairSums
      hβ n v w e0 Ω

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_inCurrent_add_beta_mul_outsideCurrent
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m =
      β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m +
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_switchedTotalPairCardEmptySourcePairSummand,
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_inCurrent_add_beta_mul_outsideCurrent
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m =
      β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m +
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_switchedTotalPairCardInnerPairSourcePairSummand,
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent]
  ring

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m ≤
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m := by
  have hle :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β
          n v w e0 m ≤
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v w e0 m :=
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_totalPairCardEmptySourcePairSummand
      hβ e0 m
  have hmul := mul_le_mul_of_nonneg_left hle hβ
  rwa [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_switchedSourceSectorResidualMomentEmptyBranchSummand]
    at hmul

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m := by
  have hle :
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
          n v w e0 m :=
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_totalPairCardInnerPairSourcePairSummand
      hβ e0 m
  have hmul := mul_le_mul_of_nonneg_left hle hβ
  rwa [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_switchedSourceSectorResidualMomentInnerPairBranchSummand]
    at hmul

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m ≤
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m := by
  have hle :
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m ≤
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v w e0 m :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_totalPairCardEmptySourcePairSummand
      hβ e0 m
  have hmul := mul_le_mul_of_nonneg_left hle hβ
  rwa [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_switchedSourceSectorResidualMomentEmptyBranchSummand]
    at hmul

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m := by
  have hle :
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
          n v w e0 m :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_totalPairCardInnerPairSourcePairSummand
      hβ e0 m
  have hmul := mul_le_mul_of_nonneg_left hle hβ
  rwa [
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_switchedSourceSectorResidualMomentInnerPairBranchSummand]
    at hmul

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hres :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m ≤
        ((β / 6) * W) / 768) :
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m ≤
      ((β / 6) * W) / 768 :=
  (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
    hβ e0 m).trans hres

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hres :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m ≤
        ((β / 6) * W) / 768) :
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m ≤
      ((β / 6) * W) / 768 :=
  (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
    hβ e0 m).trans hres

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hres :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m ≤
        ((β / 6) * W) / 768) :
    β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
      ((β / 6) * W) / 768 :=
  (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
    hβ e0 m).trans hres

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hres :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m ≤
        ((β / 6) * W) / 768) :
    β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m ≤
      ((β / 6) * W) / 768 :=
  (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
    hβ e0 m).trans hres

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_le_weight_div_six_div_384_of_switchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hres :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m ≤
        ((β / 6) * W) / 768) :
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
        e0 m ≤
      (W / 6) / 384 :=
  doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_le_weight_div_six_div_384_of_beta_mul_inCurrent_outsideCurrent_le_beta_div_six_weight_div_768
    (β := β) (W := W) hβ e0 m
    (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_768
      (β := β) (W := W) hβ.le e0 m hres)
    (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_768
      (β := β) (W := W) hβ.le e0 m hres)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_le_weight_div_six_div_384_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hres :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m ≤
        ((β / 6) * W) / 768) :
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
        w e0 m ≤
      (W / 6) / 384 :=
  doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_le_weight_div_six_div_384_of_beta_mul_inCurrent_outsideCurrent_le_beta_div_six_weight_div_768
    (β := β) (W := W) hβ e0 m
    (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_768
      (β := β) (W := W) hβ.le e0 m hres)
    (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_768
      (β := β) (W := W) hβ.le e0 m hres)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand β
          n v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
        hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
        hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
        hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m := by
  exact
    Finset.sum_le_sum (fun m _hm =>
      beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
        hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_finset_sum_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hres :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          w e0 m) ≤
        ((β / 6) * W) / 768) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m) ≤
      ((β / 6) * W) / 768 :=
  (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand
    hβ e0 Ω).trans hres

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_finset_sum_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hres :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          w e0 m) ≤
        ((β / 6) * W) / 768) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m) ≤
      ((β / 6) * W) / 768 :=
  (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand
    hβ e0 Ω).trans hres

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hres :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m) ≤
        ((β / 6) * W) / 768) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) ≤
      ((β / 6) * W) / 768 :=
  (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
    hβ e0 Ω).trans hres

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hres :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m) ≤
        ((β / 6) * W) / 768) :
    (∑ m ∈ Ω,
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) ≤
      ((β / 6) * W) / 768 :=
  (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
    hβ e0 Ω).trans hres

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_finset_sum_le_weight_div_six_div_768
    {β W : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hin :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v w e0 m) ≤
        (W / 6) / 768)
    (hout :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v w e0 m) ≤
        (W / 6) / 768) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m) ≤
      (W / 6) / 384 := by
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m) =
        (∑ m ∈ Ω,
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m) +
          ∑ m ∈ Ω,
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v w e0 m := by
          rw [
            doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_eq_inCurrent_add_outsideCurrent]
    _ ≤ (W / 6) / 768 + (W / 6) / 768 := add_le_add hin hout
    _ = (W / 6) / 384 := by ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_finset_sum_le_weight_div_six_div_768
    {β W : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hin :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) ≤
        (W / 6) / 768)
    (hout :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v w e0 m) ≤
        (W / 6) / 768) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
        n v w e0 m) ≤
      (W / 6) / 384 := by
  calc
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
        n v w e0 m) =
        (∑ m ∈ Ω,
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m) +
          ∑ m ∈ Ω,
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m := by
          rw [
            doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_eq_inCurrent_add_outsideCurrent]
    _ ≤ (W / 6) / 768 + (W / 6) / 768 := add_le_add hin hout
    _ = (W / 6) / 384 := by ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_le_weight_div_six_div_384_of_beta_mul_inCurrent_outsideCurrent_finset_sum_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hin :
      (∑ m ∈ Ω,
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m) ≤
        ((β / 6) * W) / 768)
    (hout :
      (∑ m ∈ Ω,
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m) ≤
        ((β / 6) * W) / 768) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m) ≤
      (W / 6) / 384 := by
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_finset_sum_le_weight_div_six_div_768
      (β := β) (W := W) (n := n) (v := v) (w := w) e0 Ω
      (selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
        (β := β) (W := W)
        (X :=
          ∑ m ∈ Ω,
            doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
              β n v w e0 m)
        hβ
        (by
          simpa [Finset.mul_sum, mul_assoc] using hin))
      (selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
        (β := β) (W := W)
        (X :=
          ∑ m ∈ Ω,
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v w e0 m)
        hβ
        (by
          simpa [Finset.mul_sum, mul_assoc] using hout))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_le_weight_div_six_div_384_of_beta_mul_inCurrent_outsideCurrent_finset_sum_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hin :
      (∑ m ∈ Ω,
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m) ≤
        ((β / 6) * W) / 768)
    (hout :
      (∑ m ∈ Ω,
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m) ≤
        ((β / 6) * W) / 768) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
        n v w e0 m) ≤
      (W / 6) / 384 := by
  exact
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_finset_sum_le_weight_div_six_div_768
      (β := β) (W := W) (n := n) (v := v) (w := w) e0 Ω
      (selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
        (β := β) (W := W)
        (X :=
          ∑ m ∈ Ω,
            doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m)
        hβ
        (by
          simpa [Finset.mul_sum, mul_assoc] using hin))
      (selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
        (β := β) (W := W)
        (X :=
          ∑ m ∈ Ω,
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m)
        hβ
        (by
          simpa [Finset.mul_sum, mul_assoc] using hout))

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_le_weight_div_six_div_384_of_switchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hres :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          w e0 m) ≤
        ((β / 6) * W) / 768) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        w e0 m) ≤
      (W / 6) / 384 :=
  doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_le_weight_div_six_div_384_of_beta_mul_inCurrent_outsideCurrent_finset_sum_le_beta_div_six_weight_div_768
    (β := β) (W := W) hβ e0 Ω
    (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_finset_sum_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_le_beta_div_six_weight_div_768
      (β := β) (W := W) hβ.le e0 Ω hres)
    (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_finset_sum_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_le_beta_div_six_weight_div_768
      (β := β) (W := W) hβ.le e0 Ω hres)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_le_weight_div_six_div_384_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_le_beta_div_six_weight_div_768
    {β W : ℝ} (hβ : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hres :
      (∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m) ≤
        ((β / 6) * W) / 768) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand β
        n v w e0 m) ≤
      (W / 6) / 384 :=
  doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_le_weight_div_six_div_384_of_beta_mul_inCurrent_outsideCurrent_finset_sum_le_beta_div_six_weight_div_768
    (β := β) (W := W) hβ e0 Ω
    (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_le_beta_div_six_weight_div_768
      (β := β) (W := W) hβ.le e0 Ω hres)
    (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_finset_sum_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_le_beta_div_six_weight_div_768
      (β := β) (W := W) hβ.le e0 Ω hres)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_origin_absent_on_copies
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        IsingFK.boxOrigin 3 (2 * n) ∉
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w e0
        m =
      0 := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_switchedTotalPairCardEmptySourcePairSummand]
  rw [
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_copies
      β e0 m hov habsent]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w e0
        m =
      0 :=
  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_origin_absent_on_copies
    β e0 m hov
    (fluxEdgeCopy_endsM_not_mem_of_edge_support_absent
      (FK.boxGraph 3 (2 * n)) habsent)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_origin_absent_on_copies
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        IsingFK.boxOrigin 3 (2 * n) ∉
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m =
      0 := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_switchedTotalPairCardInnerPairSourcePairSummand]
  rw [
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_copies
      β e0 m how habsent]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m =
      0 :=
  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_origin_absent_on_copies
    β e0 m how
    (fluxEdgeCopy_endsM_not_mem_of_edge_support_absent
      (FK.boxGraph 3 (2 * n)) habsent)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w e0
        m =
      0 :=
  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_origin_absent_on_edge_support
    β e0 m hov
    (doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
      hnot)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m =
      0 :=
  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_origin_absent_on_edge_support
    β e0 m how
    (doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
      hnot)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov hnot

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m how hnot

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ m ∈ Ω,
        ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
          m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m hov (habsent m hm)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ m ∈ Ω,
        ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
          m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    (∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m how (habsent m hm)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_selectedEdgeCopies_eq_zero
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
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
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_switchedTotalPairCardEmptySourcePairSummand]
  rw [
    doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
      β e0 k hedge hov how]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_selectedEdgeCopies_eq_zero
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
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
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
      e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  rw [
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_switchedTotalPairCardInnerPairSourcePairSummand]
  rw [
    doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
      β e0 k hedge hov how]
  ring

end Exact3D
end StatMech
