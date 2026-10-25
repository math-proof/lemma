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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part75
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_sourceSectorResidualMomentTsumBoundAt_expectationJSplitAt
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hweighted :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentTsumBoundAt
        β n)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  rcases hweighted with ⟨hsum, hbound⟩
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_sourceSectorResidualMomentBranchSummandTsumBound_expectationJSplit
      hβpos hsum hbound hJsplit

end Exact3D
end StatMech
