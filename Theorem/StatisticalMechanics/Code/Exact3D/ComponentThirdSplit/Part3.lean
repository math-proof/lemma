/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part2
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hmajor β hβpos hβc, hsum β hβpos hβc] with
    n hnmajor hnsum
  intro H hH Ω v hv
  exact (hnmajor H hH Ω v hv).trans (hnsum H hH Ω v hv)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
        hmajor hsum))

set_option linter.style.longLine false in


theorem firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
        hmajor hsum))

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
        hmajor hsum))

end Exact3D
end StatMech
