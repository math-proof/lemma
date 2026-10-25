/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


noncomputable def toClosedMetricFlatSurfaceGraphAtlas
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G) :
    ClosedMetricFlatSurfaceGraphAtlas g Cone G where
  cellular := atlas.cellular
  genus_eq := atlas.genus_eq
  angle := atlas.angle
  edgeClass := atlas.edgeClass
  degree_le_three := atlas.degree_le_three
  angle_reverse := atlas.angle_reverse
  transition_nonantipodal := atlas.transition_nonantipodal
  disjoint_edge_intersection := atlas.disjoint_edge_intersection
  coneOrder := atlas.coneOrder
  coneOrder_odd := atlas.coneOrder_odd
  regularTurnCorrection := fun p =>
    atlas.developedPolygonHalf p + atlas.chartRegularTurnCorrection p
  developedConeSupport := atlas.developedConeSupport
  developedGaussBonnet := atlas.developedGaussBonnet


end ClosedPolygonalFlatSurfaceGraphAtlas
end StatMech.FrontierA
