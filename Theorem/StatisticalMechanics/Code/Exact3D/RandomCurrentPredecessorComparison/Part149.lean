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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part141
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeWitnessSixthNonnegativeRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeWitnessSixthNonnegativeRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κEmpty, κInner, emptyCaseSet, emptyCaseOf, emptyRowBound,
      emptyRelaxedBudget, innerCaseSet, innerCaseOf, innerRowBound,
      innerRelaxedBudget, hcoverEmpty, hcoverInner, hpointEmpty,
      hpointInner, hrelaxEmpty, hrelaxInner, hnonnegEmpty, hnonnegInner,
      htotalEmpty, htotalInner⟩
  refine
    ⟨κEmpty, κInner, emptyCaseSet, emptyCaseOf, emptyRowBound,
      emptyRelaxedBudget, innerCaseSet, innerCaseOf, innerRowBound,
      innerRelaxedBudget, ?_, ?_, ?_, ?_, hrelaxEmpty, hrelaxInner, ?_,
      ?_⟩
  · intro ew hew m hm
    exact hcoverEmpty ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew m hm
    exact hcoverInner ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew m hm
    exact hpointEmpty ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew m hm
    exact hpointInner ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew
    exact
      (finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilter_le_multiplicityFilter_of_nonneg
        (n := n) Ω ew (emptyCaseOf ew) (emptyCaseSet ew)
        (emptyRelaxedBudget ew) (hcoverEmpty ew hew)
        (hnonnegEmpty ew hew)).trans
        (htotalEmpty ew hew)
  · intro ew hew
    exact
      (finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilter_le_multiplicityFilter_of_nonneg
        (n := n) Ω ew (innerCaseOf ew) (innerCaseSet ew)
        (innerRelaxedBudget ew) (hcoverInner ew hew)
        (hnonnegInner ew hew)).trans
        (htotalInner ew hew)

end Exact3D
end StatMech
