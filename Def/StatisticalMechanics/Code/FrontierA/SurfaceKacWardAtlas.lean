/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry.Part3
import Structure.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


def ClosedFlatSurfaceGraphAtlas.AdmissibleConeAngles
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G) : Prop :=
  forall {root : V} (p : G.Walk root root), p.IsCycle ->
    atlas.developedTurningParity p =
      1 + surfaceBaseQuadraticParity
        (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset)


end StatMech.FrontierA
