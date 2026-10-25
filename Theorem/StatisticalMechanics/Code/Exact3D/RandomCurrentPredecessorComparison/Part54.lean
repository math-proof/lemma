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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part51
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedCasesAt
    {β : ℝ} {n : ℕ}
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n := by
  rcases hcases with ⟨hstrictZ, hdiagY, hstrictY⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v hvwedge hlt
    exact
      doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_edgeCopyCollapsedSum_le
        (hstrictZ v hvwedge hlt)
  · intro v hvwedge hheight hnotlt
    exact
      doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_edgeCopyCollapsedSum_le
        (hdiagY v hvwedge hheight hnotlt)
  · intro v hvwedge hlt hypos
    exact
      doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_edgeCopyCollapsedSum_le
        (hstrictY v hvwedge hlt hypos)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorSourcePairComparisonAt_of_edgeCopyCollapsedComparisonAt
    {β : ℝ} {n : ℕ}
    (hcopy :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorEdgeCopyCollapsedComparisonAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorSourcePairComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointSourcePairEmptySum_le_of_edgeCopyCollapsedSum_le
      (hcopy v hvwedge hlt hypos)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical_of_edgeCopyCollapsedCasesPositiveSubcritical
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcases β hβpos hβc) fun n hn => by
    exact
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedCasesAt
        hn


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_edgeCopyCollapsedCasesPositiveSubcritical
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_sourcePairCasesPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical_of_edgeCopyCollapsedCasesPositiveSubcritical
      hcases)


end Exact3D
end StatMech
