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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part49
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_sourcePairCasesAt
    {β : ℝ} {n : ℕ}
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n := by
  rcases hcases with ⟨hstrictZ, hdiagY, hstrictY⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v hvwedge hlt
    exact
      doubledBoxOriginToInnerEndpointCurrentSum_le_of_sourcePairEmptySum_le
        (hstrictZ v hvwedge hlt)
  · intro v hvwedge hheight hnotlt
    exact
      doubledBoxOriginToInnerEndpointCurrentSum_le_of_sourcePairEmptySum_le
        (hdiagY v hvwedge hheight hnotlt)
  · intro v hvwedge hlt hypos
    exact
      doubledBoxOriginToInnerEndpointCurrentSum_le_of_sourcePairEmptySum_le
        (hstrictY v hvwedge hlt hypos)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorCurrentSumComparisonAt_of_sourcePairComparisonAt
    {β : ℝ} {n : ℕ}
    (hpair :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorSourcePairComparisonAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorCurrentSumComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointCurrentSum_le_of_sourcePairEmptySum_le
      (hpair v hvwedge hlt hypos)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_sourcePairCasesPositiveSubcritical
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcases β hβpos hβc) fun n hn => by
    exact
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_sourcePairCasesAt
        hn


end Exact3D
end StatMech
