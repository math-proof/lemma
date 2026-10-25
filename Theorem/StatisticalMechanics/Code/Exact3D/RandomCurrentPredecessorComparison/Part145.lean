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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part137
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨Ωactive, κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget,
      innerRowBound, innerRelaxedBudget, hsubset, hactive_iff, hcover,
      hpointEmpty, hpointInner, hrelaxEmpty, hrelaxInner, htotalEmpty,
      htotalInner⟩
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w := by
    simpa [w] using
      boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v := by
    simpa [w] using
      boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos
  have hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) := by
    simpa [w] using
      boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
        (by omega : n ≤ 2 * n) v hvwedge hlt hypos
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        (n := n) (v := v) (w := w) hvwedge hwwedge hheight hadj with
    ⟨_edge, _hedge, hov, how, _hvw⟩
  have howPred :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    simpa [w] using how
  refine
    ⟨Ωactive, κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget,
      innerRowBound, innerRelaxedBudget, hsubset, ?_, ?_, hcover, hpointEmpty,
      hpointInner, hrelaxEmpty, hrelaxInner, htotalEmpty, htotalInner⟩
  · intro m hm hnot_mem
    have hnotActive : ¬ doubledBoxOriginTouchesEdgeSupport n m := by
      intro hactive
      exact hnot_mem ((hactive_iff m hm).2 hactive)
    exact
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
        (β := β) (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
        hov hnotActive
  · intro m hm hnot_mem
    have hnotActive : ¬ doubledBoxOriginTouchesEdgeSupport n m := by
      intro hactive
      exact hnot_mem ((hactive_iff m hm).2 hactive)
    exact
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
        (β := β) (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
        howPred hnotActive

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
      htable)

end Exact3D
end StatMech
