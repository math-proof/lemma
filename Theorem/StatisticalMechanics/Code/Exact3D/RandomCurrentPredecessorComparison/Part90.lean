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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part82
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt_of_sourceSectorResidualMomentBranchComponentEmptyFiniteCutoffBoundAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hres :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  exact
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_le_of_sourceSectorResidualMomentEmptyBranchSummand_sum_bound
      (β := β) (n := n) (v := v)
      (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
      hβ Ω e0 (hres v hvwedge hlt hypos e0 hedge Ω)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt_of_sourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffBoundAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hres :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  exact
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_le_of_sourceSectorResidualMomentInnerPairBranchSummand_sum_bound
      (β := β) (n := n) (v := v)
      (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
      hβ Ω e0 (hres v hvwedge hlt hypos e0 hedge Ω)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hres :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt_of_sourceSectorResidualMomentBranchComponentEmptyFiniteCutoffBoundAt
      hβ hres.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt_of_sourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffBoundAt
      hβ hres.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundAt_of_emptyFiniteCutoffBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hfinite :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  refine tsum_le_of_all_finset_sum_le ?_ ?_
  · exact
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
        hβ n v w e0
  · intro Ω
    exact hfinite v hvwedge hlt hypos e0 hedge Ω

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundAt_of_innerPairFiniteCutoffBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hfinite :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  refine tsum_le_of_all_finset_sum_le ?_ ?_
  · exact
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
        hβ n v w e0
  · intro Ω
    exact hfinite v hvwedge hlt hypos e0 hedge Ω

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hfinite :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundAt_of_emptyFiniteCutoffBoundAt
      hβ hfinite.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundAt_of_innerPairFiniteCutoffBoundAt
      hβ hfinite.2⟩

end Exact3D
end StatMech
