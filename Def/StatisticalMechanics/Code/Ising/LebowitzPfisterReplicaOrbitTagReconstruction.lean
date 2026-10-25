/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitTagReconstruction
open Finset


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaTaggedRowProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  profileFlux (lpReplicaCurrentGraph G sites) m
    (lpReplicaRowCopies G sites m tag row)


def lpReplicaTaggedOriginProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  if row then
    fun e => lpReplicaTaggedRowProfile G sites m tag true
      (lpReplicaCurrentEdgeReflect G sites e)
  else lpReplicaTaggedRowProfile G sites m tag false


end
end StatMech.Ising
