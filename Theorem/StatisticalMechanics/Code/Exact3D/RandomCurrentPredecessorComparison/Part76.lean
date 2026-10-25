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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part68
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitAt_of_expectationJRatioGapAt
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hratio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    expectationJ_split_le_of_ratio_add_le_one
      (doubledBoxOriginToInnerEndpointExpectationJ_pos_of_strictSectorYPredecessor3
        hβpos v hvwedge hlt hypos)
      (by simpa using hratio v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapAt_of_expectationJSplitAt
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    ratio_add_le_one_of_expectationJ_split_le
      (doubledBoxOriginToInnerEndpointExpectationJ_pos_of_strictSectorYPredecessor3
        hβpos v hvwedge hlt hypos)
      (by simpa using hsplit v hvwedge hlt hypos)

end Exact3D
end StatMech
