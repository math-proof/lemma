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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part136
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨active, hactive, κ, caseSet, caseOf, emptyRowBound,
      emptyRelaxedBudget, innerRowBound, innerRelaxedBudget, hzeroEmpty,
      hzeroInner, hcover, hpointEmpty, hpointInner, hrelaxEmpty, hrelaxInner,
      htotalEmpty, htotalInner⟩
  letI : DecidablePred active := hactive
  refine
    ⟨Ω.filter active, κ, caseSet, caseOf, emptyRowBound,
      emptyRelaxedBudget, innerRowBound, innerRelaxedBudget,
      Finset.filter_subset active Ω, ?_, ?_, hcover, hpointEmpty, hpointInner,
      hrelaxEmpty, hrelaxInner, htotalEmpty, htotalInner⟩
  · exact
      finset_zeroOutside_filter_of_zeroOn_not Ω
        (fun m =>
          doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
        active hzeroEmpty
  · exact
      finset_zeroOutside_filter_of_zeroOn_not Ω
        (fun m =>
          doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
        active hzeroInner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
      htable)

end Exact3D
end StatMech
