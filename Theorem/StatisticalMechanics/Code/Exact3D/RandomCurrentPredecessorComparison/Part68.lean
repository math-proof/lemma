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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part61
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageMultiplicityPreservingRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeRelabelRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeVertexRelabelRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeVertexRelabelRows
      hβ P.table P.rows_sound

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRows
      hβ P.table P.rows_sound

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRows
      hβ P.table P.rows_sound


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeVertexRelabelEndpointMapRows
      hβ P.table P.rows_sound


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRows
      hβ P.table P.rows_sound


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRows
      hβ P.table P.rows_sound


end Exact3D
end StatMech
