/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v

namespace ClosedMetricFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


noncomputable def toClosedFlatSurfaceGraphAtlas
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) :
    ClosedFlatSurfaceGraphAtlas g G where
  cellular := atlas.cellular
  genus_eq := atlas.genus_eq
  phase := atlas.phase
  direction := atlas.direction
  edgeClass := atlas.edgeClass
  degree_le_three := atlas.degree_le_three
  direction_ne_zero := atlas.direction_ne_zero
  direction_reverse := atlas.direction_reverse
  phase_sq_eq_direction_div := fun dart next _ _ =>
    atlas.phase_sq_eq_direction_div dart next
  phase_reverse := atlas.phase_reverse
  disjoint_edge_intersection := atlas.disjoint_edge_intersection
  developedTurningParity := atlas.developedTurningParity
  developed_phase_product := atlas.developed_phase_product


end ClosedMetricFlatSurfaceGraphAtlas
end StatMech.FrontierA
