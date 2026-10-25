/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part4
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {E D Q : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]


namespace MetricCriticalIsoradialClosedFlatSurfaceEmbedding

variable {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {DualVertex Qprimal Qdual : Type u}
  [Fintype DualVertex] [DecidableEq DualVertex]
  [Fintype Qprimal] [DecidableEq Qprimal]
  [Fintype Qdual] [DecidableEq Qdual]


theorem surface_kacWard_arf_formula
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G
          embedding.toCriticalIsoradialClosedFlatSurfaceEmbedding.atlas.phase
          embedding.polygonalAtlas.edgeClass lambda
          (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G embedding.polygonalAtlas.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G embedding.polygonalAtlas.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G
                embedding.polygonalAtlas.edgeClass weight) lambda := by
  exact embedding.toCriticalIsoradialClosedFlatSurfaceEmbedding
    |>.surface_kacWard_arf_formula weight


theorem normalized_kacWard_duality
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - embedding.theta edge) *
        (1 - embedding.dualKacWard).det =
      kwIsoradialDualityNormalization V embedding.theta *
        (1 - embedding.primalKacWard).det :=
  embedding.toCriticalIsoradialClosedFlatSurfaceEmbedding
    |>.normalized_kacWard_duality

end MetricCriticalIsoradialClosedFlatSurfaceEmbedding
end StatMech.FrontierA
