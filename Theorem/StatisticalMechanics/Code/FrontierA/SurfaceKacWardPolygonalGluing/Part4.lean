/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalGluing.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalGluingFlatSurfaceEmbedding

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem developedGaussBonnet
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwClosedWalkAngleRotationNumber embedding.angle p =
      1 + (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology embedding.edgeClass p.edges.toFinset)).val +
      2 * (embedding.toClosedPolygonalFlatSurfaceGraphAtlas.developedPolygonHalf p +
        embedding.chartRegularTurnCorrection p) +
      ∑ cone ∈ embedding.developedConeSupport p,
        (embedding.coneOrder cone - 1) := by
  simpa [toClosedPolygonalFlatSurfaceGraphAtlas] using
    embedding.toClosedPolygonalFlatSurfaceGraphAtlas.developedGaussBonnet p hp


theorem kacWard_arf_formula
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G
          (ClosedMetricFlatSurfaceGraphAtlas.phase
            (ClosedPolygonalFlatSurfaceGraphAtlas.toClosedMetricFlatSurfaceGraphAtlas
                embedding.toClosedPolygonalFlatSurfaceGraphAtlas))
          embedding.edgeClass lambda
          (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G embedding.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G embedding.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G embedding.edgeClass weight)
              lambda := by
  simpa [toClosedPolygonalFlatSurfaceGraphAtlas] using
    embedding.toClosedPolygonalFlatSurfaceGraphAtlas.kacWard_arf_formula weight

end ClosedPolygonalGluingFlatSurfaceEmbedding
end StatMech.FrontierA
