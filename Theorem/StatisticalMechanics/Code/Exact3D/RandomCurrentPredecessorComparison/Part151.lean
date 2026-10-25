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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part143
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical_of_selectedCopyEmptyBoundPositiveSubcritical_selectedCopyInnerPairBoundPositiveSubcritical
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono
    ((hempty β hβpos hβc).and (hinner β hβpos hβc)) fun _n hn =>
      ⟨hn.1, hn.2⟩

end Exact3D
end StatMech
