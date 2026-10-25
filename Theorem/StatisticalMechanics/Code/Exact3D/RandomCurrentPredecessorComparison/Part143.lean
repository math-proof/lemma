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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part135
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt_of_selectedCopyEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨active, hactive, κ, caseSet, caseOf, rowBound, relaxedBudget,
      hzeroInactive, hcover, hpoint, hrelax, htotal⟩
  letI : DecidablePred active := hactive
  refine
    ⟨Ω.filter active, κ, caseSet, caseOf, rowBound, relaxedBudget,
      Finset.filter_subset active Ω, ?_, hcover, hpoint, hrelax, htotal⟩
  exact
    finset_zeroOutside_filter_of_zeroOn_not Ω
      (fun m =>
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      active hzeroInactive

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt_of_selectedCopyInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨active, hactive, κ, caseSet, caseOf, rowBound, relaxedBudget,
      hzeroInactive, hcover, hpoint, hrelax, htotal⟩
  letI : DecidablePred active := hactive
  refine
    ⟨Ω.filter active, κ, caseSet, caseOf, rowBound, relaxedBudget,
      Finset.filter_subset active Ω, ?_, hcover, hpoint, hrelax, htotal⟩
  exact
    finset_zeroOutside_filter_of_zeroOn_not Ω
      (fun m =>
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      active hzeroInactive

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt_of_selectedCopyEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
      htable.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt_of_selectedCopyInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
      htable.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
      htable)

end Exact3D
end StatMech
