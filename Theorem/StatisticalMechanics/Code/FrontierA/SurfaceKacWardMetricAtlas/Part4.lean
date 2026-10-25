/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedMetricFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem direction_ne_zero
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) (dart : G.Dart) :
    atlas.direction dart ≠ 0 := by
  exact Circle.coe_ne_zero _

theorem direction_reverse
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) (dart : G.Dart) :
    atlas.direction dart.symm = -atlas.direction dart := by
  unfold direction
  rw [atlas.angle_reverse]
  simp [Real.Angle.coe_toCircle]

theorem phase_sq_eq_direction_div
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    (dart next : G.Dart) :
    atlas.phase dart next ^ 2 =
      atlas.direction next / atlas.direction dart := by
  exact kwAngleTurnPhase_sq_eq_toCircle_div _ _

theorem phase_reverse
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    (dart next : G.Dart) (hadj : G.DartAdj dart next)
    (hne : dart.edge ≠ next.edge) :
    atlas.phase next.symm dart.symm = (atlas.phase dart next)⁻¹ := by
  unfold phase
  rw [atlas.angle_reverse, atlas.angle_reverse]
  exact kwAngleTurnPhase_reverse_add_pi _ _
    (atlas.transition_nonantipodal dart next hadj hne)

end ClosedMetricFlatSurfaceGraphAtlas
end StatMech.FrontierA
