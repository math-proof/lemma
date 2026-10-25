/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaPooledSelectedSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  profile : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat
  orbit : lpReplicaSymmetrizedProfile G sites profile = q
  selected : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat
  selected_le : selected <= profile
  slots : LPReplicaProfileOrbitSlotState G sites q
  realizes : LPReplicaProfileOrbitSlotRealizes G sites q
    profile selected slots

end
end StatMech.Ising
