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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part59
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.not_vertexEquivStrictZ_eq_refl
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))})
    (hrow : T.rowPred (T.classifyStrictZ p))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    T.vertexEquivStrictZ p hrow m ≠ Equiv.refl (FK.boxVerts 3 (2 * n)) := by
  intro hφ
  let w := boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w :=
    boxVertStrictSectorPredecessor3_wedge p.val p.property.1 p.property.2
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 p.val :=
    boxVertStrictSectorPredecessor3_height_lt p.val p.property.1 p.property.2
  have hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) :=
    boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2
  have hsource_ne :
      doubledBoxOriginToInnerEndpointSource n p.val ≠
        doubledBoxOriginToInnerEndpointSource n w :=
    doubledBoxOriginToInnerEndpointSource_ne_of_orderedWedge_lowerDoubledAdj
      p.property.1 hwwedge hheight hadj
  have hsource_eq :
      doubledBoxOriginToInnerEndpointSource n p.val =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [w, hφ] using T.sourceStrictZ p hrow m
  exact hsource_ne hsource_eq

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.not_vertexEquivDiagY_eq_refl
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))})
    (hrow : T.rowPred (T.classifyDiagY p))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    T.vertexEquivDiagY p hrow m ≠ Equiv.refl (FK.boxVerts 3 (2 * n)) := by
  intro hφ
  let w :=
    boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
      p.property.2.2
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w :=
    boxVertDiagonalPredecessor3_wedge p.val p.property.1 p.property.2.1
      p.property.2.2
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 p.val :=
    boxVertDiagonalPredecessor3_height_lt p.val p.property.1 p.property.2.1
      p.property.2.2
  have hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) :=
    boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2.1
      p.property.2.2
  have hsource_ne :
      doubledBoxOriginToInnerEndpointSource n p.val ≠
        doubledBoxOriginToInnerEndpointSource n w :=
    doubledBoxOriginToInnerEndpointSource_ne_of_orderedWedge_lowerDoubledAdj
      p.property.1 hwwedge hheight hadj
  have hsource_eq :
      doubledBoxOriginToInnerEndpointSource n p.val =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [w, hφ] using T.sourceDiagY p hrow m
  exact hsource_ne hsource_eq

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.not_vertexEquivStrictY_eq_refl
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))})
    (hrow : T.rowPred (T.classifyStrictY p))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    T.vertexEquivStrictY p hrow m ≠ Equiv.refl (FK.boxVerts 3 (2 * n)) := by
  intro hφ
  let w :=
    boxVertStrictSectorYPredecessor3 p.val p.property.1 p.property.2.1
      p.property.2.2
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w :=
    boxVertStrictSectorYPredecessor3_wedge p.val p.property.1
      p.property.2.1 p.property.2.2
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 p.val :=
    boxVertStrictSectorYPredecessor3_height_lt p.val p.property.1
      p.property.2.1 p.property.2.2
  have hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) :=
    boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2.1
      p.property.2.2
  have hsource_ne :
      doubledBoxOriginToInnerEndpointSource n p.val ≠
        doubledBoxOriginToInnerEndpointSource n w :=
    doubledBoxOriginToInnerEndpointSource_ne_of_orderedWedge_lowerDoubledAdj
      p.property.1 hwwedge hheight hadj
  have hsource_eq :
      doubledBoxOriginToInnerEndpointSource n p.val =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [w, hφ] using T.sourceStrictY p hrow m
  exact hsource_ne hsource_eq


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T : OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorInjectionRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt.toSourceSectorInjectionRowsAt
      T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageMultiplicityPreservingRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.toSourceSectorImageRowsAt
      (β := β) T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeRelabelRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt.toSourceSectorImageRowsAt
      (β := β) T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T : OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorInjectionRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt.toSourceSectorInjectionRowsAt
      T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageMultiplicityPreservingRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.toSourceSectorImageRowsAt
      (β := β) T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeRelabelRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt.toSourceSectorImageRowsAt
      (β := β) T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T : OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorInjectionRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt.toSourceSectorInjectionRowsAt
      T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageMultiplicityPreservingRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.toSourceSectorImageRowsAt
      (β := β) T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeRelabelRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt.toSourceSectorImageRowsAt
      (β := β) T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeVertexRelabelRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeRelabelRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.toSourceSectorImageEdgeRelabelRowsAt
      T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeRelabelRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.toSourceSectorImageEdgeRelabelRowsAt
      T)
    hrows


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeRelabelRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.toSourceSectorImageEdgeRelabelRowsAt
      T)
    hrows

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeVertexRelabelEndpointMapRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesAt_of_sourceSectorImageEdgeVertexRelabelRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.of_maps_origin_endpoint
      T)
    hrows

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.of_maps_origin_endpoint
      T)
    hrows

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRows
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.of_maps_origin_endpoint
      T)
    hrows


end Exact3D
end StatMech
