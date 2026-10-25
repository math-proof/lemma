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
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part5
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


variable {V : Type*} [Fintype V] [DecidableEq V]


def ghsvp_someSet (A : Finset V) : Finset (Option V) := A.map someEmb


def ghsvp_fieldSet (A : Finset V) : Finset (Option V) := insert none (ghsvp_someSet A)


noncomputable def ghsvp_subsetMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) : Real :=
  let J2 := ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)
  ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet A) *
    ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Aᶜ)

end StatMech.Ising
