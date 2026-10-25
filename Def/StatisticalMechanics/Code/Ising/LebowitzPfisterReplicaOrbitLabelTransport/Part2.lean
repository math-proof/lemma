/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaProfileOrbitSlotMoveEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaProfileOrbitSlotState G sites q ≃
      LPReplicaProfileOrbitSlotState G sites q where
  toFun := lpReplicaProfileOrbitSlotMove G sites q
  invFun := lpReplicaProfileOrbitSlotMove G sites q
  left_inv := lpReplicaProfileOrbitSlotMove_involutive G sites q
  right_inv := lpReplicaProfileOrbitSlotMove_involutive G sites q


def LPReplicaProfileOrbitSlotRealizes
    (G : SimpleGraph V) (sites : I -> V)
    (q m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaProfileOrbitSlotState G sites q) : Prop :=
  forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    (s.allocation e).card = m e.1 ∧
      (s.selectedRep e).card = p e.1 ∧
      (s.selectedReflect e).card =
        p (lpReplicaCurrentEdgeReflect G sites e.1)


end
end StatMech.Ising
