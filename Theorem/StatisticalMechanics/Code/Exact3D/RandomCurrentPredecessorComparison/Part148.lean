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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part140
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  classical
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    fun m => doubledBoxOriginTouchesEdgeSupport n m
  let Ωactive :=
    Ω.filter active
  rcases htable v hvwedge hlt hypos e0 hedge Ωactive with
    ⟨κ, ownerCaseSet, ownerCaseOf, ownerEmptyRowBound,
      ownerEmptyRelaxedBudget, ownerInnerRowBound, ownerInnerRelaxedBudget,
      hcoverOwner, hpointEmptyOwner, hpointInnerOwner, hrelaxEmptyOwner,
      hrelaxInnerOwner, htotalEmptyOwner, htotalInnerOwner⟩
  let Fempty :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
  let Finner :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
  have hsumEmpty :
      Finset.sum Ωactive Fempty ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
    exact
      finset_sum_le_of_doubledBoxOriginIncidentEdgeOwnerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
        (n := n) (κ := κ) Ωactive Fempty ownerCaseOf ownerCaseSet
        ownerEmptyRowBound ownerEmptyRelaxedBudget
        (by
          intro m hm hnot
          have hmFilter : m ∈ Ω.filter active := by
            simpa [Ωactive] using hm
          have hactive : doubledBoxOriginTouchesEdgeSupport n m := by
            simpa [active] using (Finset.mem_filter.mp hmFilter).2
          exact (hnot hactive).elim)
        hcoverOwner hpointEmptyOwner hrelaxEmptyOwner htotalEmptyOwner
  have hsumInner :
      Finset.sum Ωactive Finner ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := by
    exact
      finset_sum_le_of_doubledBoxOriginIncidentEdgeOwnerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
        (n := n) (κ := κ) Ωactive Finner ownerCaseOf ownerCaseSet
        ownerInnerRowBound ownerInnerRelaxedBudget
        (by
          intro m hm hnot
          have hmFilter : m ∈ Ω.filter active := by
            simpa [Ωactive] using hm
          have hactive : doubledBoxOriginTouchesEdgeSupport n m := by
            simpa [active] using (Finset.mem_filter.mp hmFilter).2
          exact (hnot hactive).elim)
        hcoverOwner hpointInnerOwner hrelaxInnerOwner htotalInnerOwner
  refine
    ⟨Ωactive, (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ), Ωactive,
      (fun m => m), Fempty, Fempty, Finner, Finner, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
  · simp [Ωactive]
  · intro m hm
    simp [Ωactive, active, hm]
  · intro m hm
    exact hm
  · intro m _hm
    exact le_rfl
  · intro m _hm
    exact le_rfl
  · intro c _hc
    exact le_rfl
  · intro c _hc
    exact le_rfl
  · calc
      finiteSupportExplicitCaseBudgetTotal Ωactive (fun m => m) Ωactive
          Fempty =
        Finset.sum Ωactive Fempty :=
          finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum Ωactive
            Fempty
      _ ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v :=
        hsumEmpty
  · calc
      finiteSupportExplicitCaseBudgetTotal Ωactive (fun m => m) Ωactive
          Finner =
        Finset.sum Ωactive Finner :=
          finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum Ωactive
            Finner
      _ ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
        hsumInner

end Exact3D
end StatMech
