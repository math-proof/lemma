/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaPooledSelectedSlotMove_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Involutive (lpReplicaPooledSelectedSlotMove G sites q) := by
  intro z
  apply LPReplicaPooledSelectedSlotState.ext
  · exact lpReplicaPartialReflectProfile_involutive
      G sites z.profile z.selected z.selected_le
  · funext e
    exact congrArg z.selected
      (lpReplicaCurrentEdgeReflect_involutive G sites e)
  · exact lpReplicaProfileOrbitSlotMove_involutive G sites q z.slots


end
end StatMech.Ising
