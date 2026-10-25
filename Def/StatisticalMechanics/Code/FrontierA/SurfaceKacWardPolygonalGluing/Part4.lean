/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalGluing.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalGluingFlatSurfaceEmbedding

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


noncomputable def toClosedPolygonalFlatSurfaceGraphAtlas
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G) :
    ClosedPolygonalFlatSurfaceGraphAtlas g Cone G where
  cellular := embedding.cellular
  genus_eq := embedding.genus_eq
  angle := embedding.angle
  edgeClass := embedding.edgeClass
  degree_le_three := embedding.degree_le_three
  angle_reverse := embedding.angle_reverse
  transition_nonantipodal := embedding.transition_nonantipodal
  disjoint_edge_intersection := embedding.disjoint_edge_intersection
  coneOrder := embedding.coneOrder
  coneOrder_odd := embedding.coneOrder_odd
  developedConeSupport := embedding.developedConeSupport
  chartRegularTurnCorrection := embedding.chartRegularTurnCorrection
  developedPolygon := embedding.developedPolygon
  chartTransitionIndex := embedding.chartTransitionIndex
  developedTurnLift := embedding.developedTurnLift_constructed
  chartIndexGaussBonnet := embedding.chartIndexGaussBonnet


end ClosedPolygonalGluingFlatSurfaceEmbedding
end StatMech.FrontierA
