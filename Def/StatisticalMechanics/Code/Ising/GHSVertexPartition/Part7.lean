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
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part7
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def ghsvp_disagreementCorr (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : Real) (o x : V) (A : Finset V) : Real :=
  if o ∈ A ∨ x ∈ A then 0
  else ghsvp_vertexCorr G.edgeFinset (fun _ => 2 * β) Aᶜ {o, x}


noncomputable def ghsvp_agreementMag (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (y : V) (A : Finset V) : Real :=
  if y ∈ A then
    ghsvp_vertexCorrField G.edgeFinset (fun _ => 2 * β) (fun _ => 2 * β * h) A {y}
  else 0

end StatMech.Ising
