module
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part6
public import Theorem.StatisticalMechanics.Code.Sharpness.SimonLieb.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


def lpReplicaCurrentLeftEmbedding : V ↪ LPReplicaCurrentVertex V where
  toFun x := .inl (.inl x)
  inj' := fun _ _ h => Sum.inl.inj (Sum.inl.inj h)


def lpReplicaCurrentLeftSide : Finset (LPReplicaCurrentVertex V) :=
  insert lpReplicaCurrentGhost0
    (Finset.univ.map lpReplicaCurrentLeftEmbedding)

end
end StatMech.Ising
