/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaPooledSelectedOrbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q} =>
    Sigma fun a : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      p <= m.1} =>
      LPReplicaProfileOrbitSelectedLabel G sites q m.1 a.1


def lpReplicaPooledSelectedOrbitLabelEquivSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaPooledSelectedOrbitLabel G sites q ≃
      LPReplicaPooledSelectedSlotState G sites q where
  toFun z := {
    profile := z.1.1
    orbit := z.1.2
    selected := z.2.1.1
    selected_le := z.2.1.2
    slots := (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
      G sites q z.1.1 z.2.1.1 z.2.2).1
    realizes := (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
      G sites q z.1.1 z.2.1.1 z.2.2).2
  }
  invFun z := ⟨⟨z.profile, z.orbit⟩, ⟨⟨z.selected, z.selected_le⟩,
    (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
      G sites q z.profile z.selected).symm ⟨z.slots, z.realizes⟩⟩⟩
  left_inv z := by
    rcases z with ⟨m, a, L⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    exact (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
      G sites q m.1 a.1).left_inv L
  right_inv z := by
    apply LPReplicaPooledSelectedSlotState.ext <;> try rfl

end
end StatMech.Ising
