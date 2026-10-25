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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part74
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical_of_finiteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hbudget :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono
    ((hbudget β hβpos hβc).and (hJsplit β hβpos hβc)) fun n hn =>
      ⟨hn.1, hn.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical
    (hcert :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcert β hβpos hβc) fun n hn =>
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_filterSwitchedSourceSectorResidualMomentExpectationJSplitAt
      hβpos hn

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hbudget :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical_of_finiteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
      hbudget hJsplit)

end Exact3D
end StatMech
