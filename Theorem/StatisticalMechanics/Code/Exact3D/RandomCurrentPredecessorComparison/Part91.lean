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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part83
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffBoundAt_of_emptyFiniteCutoffMajorantBoundAt
    {β : ℝ} {n : ℕ}
    (hmajor :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases hmajor v hvwedge hlt hypos e0 hedge Ω with
    ⟨budget, hpoint, hbudget⟩
  exact (Finset.sum_le_sum hpoint).trans hbudget

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffBoundAt_of_innerPairFiniteCutoffMajorantBoundAt
    {β : ℝ} {n : ℕ}
    (hmajor :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases hmajor v hvwedge hlt hypos e0 hedge Ω with
    ⟨budget, hpoint, hbudget⟩
  exact (Finset.sum_le_sum hpoint).trans hbudget

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffMajorantBoundsAt
    {β : ℝ} {n : ℕ}
    (hmajor :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffBoundAt_of_emptyFiniteCutoffMajorantBoundAt
      hmajor.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffBoundAt_of_innerPairFiniteCutoffMajorantBoundAt
      hmajor.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hmajor :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffMajorantBoundsAt
      hmajor)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffMajorantBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hmajor :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffMajorantBoundsAt
      hmajor)

end Exact3D
end StatMech
