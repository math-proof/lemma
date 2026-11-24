module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part3
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCurrentLeft (sites : I -> V) (i : I) :
    LPReplicaCurrentVertex V := .inl (.inl (sites i))

def lpReplicaCurrentRight (sites : I -> V) (i : I) :
    LPReplicaCurrentVertex V := .inl (.inr (sites i))

def lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V := .inr false

def lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V := .inr true


end
end StatMech.Ising
