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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part133
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt_of_selectedCopyEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨Ωactive, κ, caseSet, caseOf, rowBound, relaxedBudget, hsubset,
      hzero, hcover, hpoint, hrelax, htotal⟩
  exact
    finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_activeSubset_le_of_relaxed
      Ω Ωactive
      (fun m =>
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      caseOf caseSet rowBound relaxedBudget hsubset hzero hcover hpoint
      hrelax htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt_of_selectedCopyInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨Ωactive, κ, caseSet, caseOf, rowBound, relaxedBudget, hsubset,
      hzero, hcover, hpoint, hrelax, htotal⟩
  exact
    finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_activeSubset_le_of_relaxed
      Ω Ωactive
      (fun m =>
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      caseOf caseSet rowBound relaxedBudget hsubset hzero hcover hpoint
      hrelax htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt_of_selectedCopyEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt
      htable.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt_of_selectedCopyInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundAt
      htable.2⟩

end Exact3D
end StatMech
