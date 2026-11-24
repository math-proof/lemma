module
public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
public import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part173
open scoped BigOperators symmDiff
open MeasureTheory
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_sourceSectorCapResidualMomentExpectationJSplitAt
    {β C : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hcert :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorCapResidualMomentExpectationJSplitAt
        β C n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  rcases hcert with ⟨hC, hcap, hbudget, hJsplit⟩
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_sourceSectorCapResidualMomentTsumBudgetAt_expectationJSplitAt
      hβpos hC hcap hbudget hJsplit

end Exact3D
end StatMech
