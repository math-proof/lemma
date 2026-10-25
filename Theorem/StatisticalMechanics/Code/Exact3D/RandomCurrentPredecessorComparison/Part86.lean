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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part78
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentTsumBoundAt_of_sourceSectorResidualMomentBranchTsumBoundAt
    {β : ℝ} {n : ℕ}
    (hbranch :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchTsumBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentTsumBoundAt
      β n := by
  rcases hbranch with ⟨hempty, hinner, hbound⟩
  constructor
  · intro v hvwedge hlt hypos e0 hedge
    exact
      doubledBoxSourceSectorResidualMomentBranchSummand_summable_of_branch_summable
        (hempty v hvwedge hlt hypos e0 hedge)
        (hinner v hvwedge hlt hypos e0 hedge)
  · intro v hvwedge hlt hypos e0 hedge
    exact
      doubledBoxSourceSectorResidualMomentBranchSummand_tsum_le_of_branch_tsum_bound
        (hempty v hvwedge hlt hypos e0 hedge)
        (hinner v hvwedge hlt hypos e0 hedge)
        (hbound v hvwedge hlt hypos e0 hedge)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_sourceSectorResidualMomentBranchTsumBoundAt_expectationJSplitAt
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hbranch :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchTsumBoundAt
        β n)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_sourceSectorResidualMomentTsumBoundAt_expectationJSplitAt
    hβpos
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentTsumBoundAt_of_sourceSectorResidualMomentBranchTsumBoundAt
      hbranch)
    hJsplit

end Exact3D
end StatMech
