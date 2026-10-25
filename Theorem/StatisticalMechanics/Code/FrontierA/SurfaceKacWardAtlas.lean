/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry.Part3
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


theorem ClosedFlatSurfaceGraphAtlas.phase_sq_transport
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G)
    (dart next : G.Dart) (hadj : G.DartAdj dart next)
    (hne : dart.edge ≠ next.edge) :
    atlas.phase dart next ^ 2 * atlas.direction dart =
      atlas.direction next := by
  rw [atlas.phase_sq_eq_direction_div dart next hadj hne]
  exact div_mul_cancel₀ _ (atlas.direction_ne_zero dart)


end StatMech.FrontierA
