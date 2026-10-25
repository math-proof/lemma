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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part114
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBoundEmptyIn, rowBoundEmptyOutside,
      rowBoundInnerIn, rowBoundInnerOutside, relaxedBudgetEmptyIn,
      relaxedBudgetEmptyOutside, relaxedBudgetInnerIn,
      relaxedBudgetInnerOutside, hcover, hpointEmptyIn, hpointEmptyOutside,
      hpointInnerIn, hpointInnerOutside, hrelaxEmptyIn,
      hrelaxEmptyOutside, hrelaxInnerIn, hrelaxInnerOutside, hnonnegEmpty,
      hnonnegInner, htotalEmpty, htotalInner⟩
  refine
    ⟨κ, caseSet, caseOf, rowBoundEmptyIn, rowBoundEmptyOutside,
      rowBoundInnerIn, rowBoundInnerOutside, relaxedBudgetEmptyIn,
      relaxedBudgetEmptyOutside, relaxedBudgetInnerIn,
      relaxedBudgetInnerOutside, ?_, ?_, ?_, ?_, ?_, hrelaxEmptyIn,
      hrelaxEmptyOutside, hrelaxInnerIn, hrelaxInnerOutside, hnonnegEmpty,
      hnonnegInner, ?_, ?_⟩
  · intro ew hew
    exact
      forall_activeUpdateSelectedEdgeMultiplicityRows_of_forall_activeOriginTouchesEdgeSupportRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew (by simpa [w] using hedge) Ω (hcover ew hew)
  · intro ew hew
    exact
      forall_activeUpdateSelectedEdgeMultiplicityRows_of_forall_activeOriginTouchesEdgeSupportRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew (by simpa [w] using hedge) Ω (hpointEmptyIn ew hew)
  · intro ew hew
    exact
      forall_activeUpdateSelectedEdgeMultiplicityRows_of_forall_activeOriginTouchesEdgeSupportRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew (by simpa [w] using hedge) Ω (hpointEmptyOutside ew hew)
  · intro ew hew
    exact
      forall_activeUpdateSelectedEdgeMultiplicityRows_of_forall_activeOriginTouchesEdgeSupportRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew (by simpa [w] using hedge) Ω (hpointInnerIn ew hew)
  · intro ew hew
    exact
      forall_activeUpdateSelectedEdgeMultiplicityRows_of_forall_activeOriginTouchesEdgeSupportRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew (by simpa [w] using hedge) Ω (hpointInnerOutside ew hew)
  · intro ew hew
    exact
      (finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveUpdateSelectedEdgeMultiplicityFilter_le_activeOriginTouchesEdgeSupportFilter_of_nonneg_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew (by simpa [w] using hedge) Ω (caseOf ew) (caseSet ew)
        (fun c =>
          relaxedBudgetEmptyIn ew c + relaxedBudgetEmptyOutside ew c)
        (hcover ew hew) (hnonnegEmpty ew hew)).trans
        (htotalEmpty ew hew)
  · intro ew hew
    exact
      (finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveUpdateSelectedEdgeMultiplicityFilter_le_activeOriginTouchesEdgeSupportFilter_of_nonneg_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew (by simpa [w] using hedge) Ω (caseOf ew) (caseSet ew)
        (fun c =>
          relaxedBudgetInnerIn ew c + relaxedBudgetInnerOutside ew c)
        (hcover ew hew) (hnonnegInner ew hew)).trans
        (htotalInner ew hew)

end Exact3D
end StatMech
