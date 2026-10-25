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
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part6
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def ghsvp_tZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) : Real :=
  ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β)
    (fun x => if x ∈ A then 2 * β * h else 0)

noncomputable def ghsvp_uZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : Real) (A : Finset V) : Real :=
  ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β) (fun _ => 0)

end StatMech.Ising
