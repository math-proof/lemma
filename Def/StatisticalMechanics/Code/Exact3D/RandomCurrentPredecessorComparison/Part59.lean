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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part62
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.of_maps_origin_endpoint
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
      n Case where
  rows := T.rows
  rowPred := T.rowPred
  classifyStrictZ := T.classifyStrictZ
  classifyDiagY := T.classifyDiagY
  classifyStrictY := T.classifyStrictY
  coversStrictZ := T.coversStrictZ
  coversDiagY := T.coversDiagY
  coversStrictY := T.coversStrictY
  mapStrictZ := T.mapStrictZ
  mapStrictZ_injective := T.mapStrictZ_injective
  mapDiagY := T.mapDiagY
  mapDiagY_injective := T.mapDiagY_injective
  mapStrictY := T.mapStrictY
  mapStrictY_injective := T.mapStrictY_injective
  vertexEquivStrictZ := T.vertexEquivStrictZ
  edgeEquivStrictZ := T.edgeEquivStrictZ
  multiplicityStrictZ := T.multiplicityStrictZ
  endsStrictZ := T.endsStrictZ
  sourceStrictZ := by
    intro p hrow m
    exact
      doubledBoxOriginToInnerEndpointSource_map_eq_strictSectorPredecessor_of_maps_origin_endpoint
        p (T.vertexEquivStrictZ p hrow m)
        (T.originStrictZ p hrow m) (T.endpointStrictZ p hrow m)
  vertexEquivDiagY := T.vertexEquivDiagY
  edgeEquivDiagY := T.edgeEquivDiagY
  multiplicityDiagY := T.multiplicityDiagY
  endsDiagY := T.endsDiagY
  sourceDiagY := by
    intro p hrow m
    exact
      doubledBoxOriginToInnerEndpointSource_map_eq_diagonalPredecessor_of_maps_origin_endpoint
        p (T.vertexEquivDiagY p hrow m)
        (T.originDiagY p hrow m) (T.endpointDiagY p hrow m)
  vertexEquivStrictY := T.vertexEquivStrictY
  edgeEquivStrictY := T.edgeEquivStrictY
  multiplicityStrictY := T.multiplicityStrictY
  endsStrictY := T.endsStrictY
  sourceStrictY := by
    intro p hrow m
    exact
      doubledBoxOriginToInnerEndpointSource_map_eq_strictSectorYPredecessor_of_maps_origin_endpoint
        p (T.vertexEquivStrictY p hrow m)
        (T.originStrictY p hrow m) (T.endpointStrictY p hrow m)


noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.toSourceSectorImageEdgeRelabelRowsAt
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
        n Case) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt
      n Case where
  rows := T.rows
  rowPred := T.rowPred
  classifyStrictZ := T.classifyStrictZ
  classifyDiagY := T.classifyDiagY
  classifyStrictY := T.classifyStrictY
  coversStrictZ := T.coversStrictZ
  coversDiagY := T.coversDiagY
  coversStrictY := T.coversStrictY
  mapStrictZ := T.mapStrictZ
  mapStrictZ_injective := T.mapStrictZ_injective
  mapDiagY := T.mapDiagY
  mapDiagY_injective := T.mapDiagY_injective
  mapStrictY := T.mapStrictY
  mapStrictY_injective := T.mapStrictY_injective
  imageStrictZ := by
    intro p hrow m
    exact
      EdgeCopySourceSectorImageEmbedding.ofEdgeEquivVertexEquiv
        (T.vertexEquivStrictZ p hrow m)
        (T.edgeEquivStrictZ p hrow m)
        (T.multiplicityStrictZ p hrow m)
        (T.endsStrictZ p hrow m)
        (T.sourceStrictZ p hrow m)
  edgeEquivStrictZ := T.edgeEquivStrictZ
  multiplicityStrictZ := T.multiplicityStrictZ
  imageDiagY := by
    intro p hrow m
    exact
      EdgeCopySourceSectorImageEmbedding.ofEdgeEquivVertexEquiv
        (T.vertexEquivDiagY p hrow m)
        (T.edgeEquivDiagY p hrow m)
        (T.multiplicityDiagY p hrow m)
        (T.endsDiagY p hrow m)
        (T.sourceDiagY p hrow m)
  edgeEquivDiagY := T.edgeEquivDiagY
  multiplicityDiagY := T.multiplicityDiagY
  imageStrictY := by
    intro p hrow m
    exact
      EdgeCopySourceSectorImageEmbedding.ofEdgeEquivVertexEquiv
        (T.vertexEquivStrictY p hrow m)
        (T.edgeEquivStrictY p hrow m)
        (T.multiplicityStrictY p hrow m)
        (T.endsStrictY p hrow m)
        (T.sourceStrictY p hrow m)
  edgeEquivStrictY := T.edgeEquivStrictY
  multiplicityStrictY := T.multiplicityStrictY

end Exact3D
end StatMech
