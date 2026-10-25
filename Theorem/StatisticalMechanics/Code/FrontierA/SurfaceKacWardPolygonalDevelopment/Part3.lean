/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem kacWard_arf_formula
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G
          atlas.toClosedMetricFlatSurfaceGraphAtlas.phase atlas.edgeClass
          lambda (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G atlas.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G atlas.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G atlas.edgeClass weight)
              lambda := by
  exact atlas.toClosedMetricFlatSurfaceGraphAtlas.kacWard_arf_formula weight

end ClosedPolygonalFlatSurfaceGraphAtlas
end StatMech.FrontierA
