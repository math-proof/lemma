/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


noncomputable def ClosedFlatSurfaceGraphAtlas.toAdmissibleEmbedding
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G)
    (hadmissible : atlas.AdmissibleConeAngles) :
    AdmissibleClosedFlatSurfaceEmbedding g G where
  geometry := atlas.toLocalSpinorGeometry
  developed_simple_cycle_holonomy := atlas.simple_cycle_holonomy hadmissible


end StatMech.FrontierA
