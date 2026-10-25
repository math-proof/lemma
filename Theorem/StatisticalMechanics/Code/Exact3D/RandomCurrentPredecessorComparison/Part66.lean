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
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part11
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAtPackage
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageRows
      hβ P.table P.rows_sound

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAtPackage
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageRowsPackage
      hβ P)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAtPackage
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_sourcePairCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
      hβ P)


end Exact3D
end StatMech
