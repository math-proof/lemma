/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


def ghsvp_vertexEdges (E : Finset (Sym2 W)) (S : Finset W) : Finset (Sym2 W) :=
  E.filter (Sharpness.edgeInside S)


noncomputable def ghsvp_vertexZ (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (S : Finset W) : Real :=
  ZJ (ghsvp_vertexEdges E S) J (fun _ => 0)

end StatMech.Ising
