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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part130
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨active, hactive, κ, caseSet, caseOf, emptyRowBound,
      emptyRelaxedBudget, _innerRowBound, _innerRelaxedBudget, hzeroEmpty,
      _hzeroInner, hcover, hpointEmpty, _hpointInner, hrelaxEmpty,
      _hrelaxInner, htotalEmpty, _htotalInner⟩
  refine ⟨active, hactive, ?_⟩
  letI : DecidablePred active := hactive
  exact
    ⟨κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget, hzeroEmpty,
      hcover, hpointEmpty, hrelaxEmpty, htotalEmpty⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨active, hactive, κ, caseSet, caseOf, _emptyRowBound,
      _emptyRelaxedBudget, innerRowBound, innerRelaxedBudget, _hzeroEmpty,
      hzeroInner, hcover, _hpointEmpty, hpointInner, _hrelaxEmpty,
      hrelaxInner, _htotalEmpty, htotalInner⟩
  refine ⟨active, hactive, ?_⟩
  letI : DecidablePred active := hactive
  exact
    ⟨κ, caseSet, caseOf, innerRowBound, innerRelaxedBudget, hzeroInner,
      hcover, hpointInner, hrelaxInner, htotalInner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
      htable,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
      htable⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
      htable)

end Exact3D
end StatMech
