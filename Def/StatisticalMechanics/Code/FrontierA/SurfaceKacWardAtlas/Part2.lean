/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


noncomputable def ClosedFlatSurfaceGraphAtlas.toLocalSpinorGeometry
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G) :
    SurfaceLocalSpinorGeometry g G where
  cellular := atlas.cellular
  genus_eq := atlas.genus_eq
  phase := atlas.phase
  direction := atlas.direction
  edgeClass := atlas.edgeClass
  degree_le_three := atlas.degree_le_three
  direction_ne_zero := atlas.direction_ne_zero
  direction_reverse := atlas.direction_reverse
  phase_sq_transport := atlas.phase_sq_transport
  phase_reverse := atlas.phase_reverse
  disjoint_edge_intersection := atlas.disjoint_edge_intersection

end StatMech.FrontierA
