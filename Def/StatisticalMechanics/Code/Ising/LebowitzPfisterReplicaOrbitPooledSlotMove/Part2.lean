/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove.Part3
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaPooledSelectedSlotMove
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaPooledSelectedSlotState G sites q) :
    LPReplicaPooledSelectedSlotState G sites q where
  profile := lpReplicaPartialReflectProfile G sites z.profile z.selected
  orbit := (lpReplicaSymmetrizedProfile_partialReflect G sites
    z.profile z.selected z.selected_le).trans z.orbit
  selected := fun e =>
    z.selected (lpReplicaCurrentEdgeReflect G sites e)
  selected_le := lpReplicaReflectSubprofile_le_partialReflectProfile
    G sites z.profile z.selected
  slots := lpReplicaProfileOrbitSlotMove G sites q z.slots
  realizes := (lpReplicaProfileOrbitSlotRealizes_move_iff
    G sites q z.profile z.selected z.selected_le z.slots).mp z.realizes


end
end StatMech.Ising
