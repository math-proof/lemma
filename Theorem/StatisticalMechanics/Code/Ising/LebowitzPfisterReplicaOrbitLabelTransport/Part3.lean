/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaProfileOrbitSlotMove_allocation_card
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaProfileOrbitSlotState G sites q)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    ((lpReplicaProfileOrbitSlotMove G sites q s).allocation e).card =
      (s.allocation e).card - (s.selectedRep e).card +
        (s.selectedReflect e).card := by
  have hdisj : Disjoint
      (s.allocation e \ s.selectedRep e) (s.selectedReflect e) := by
    rw [Finset.disjoint_left]
    intro x hx hT
    have hxalloc := (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_sdiff.mp (s.selectedReflect_subset e hT)).2 hxalloc
  change ((s.allocation e \ s.selectedRep e) ∪
    s.selectedReflect e).card = _
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_sdiff_of_subset (s.selectedRep_subset e)]


theorem lpReplicaProfileOrbitSlotRealizes_move_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hp : p <= m)
    (s : LPReplicaProfileOrbitSlotState G sites q) :
    LPReplicaProfileOrbitSlotRealizes G sites q m p s ↔
      LPReplicaProfileOrbitSlotRealizes G sites q
        (lpReplicaPartialReflectProfile G sites m p)
        (fun e => p (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaProfileOrbitSlotMove G sites q s) := by
  constructor
  · intro h e
    have he := h e
    rw [lpReplicaProfileOrbitSlotMove_allocation_card]
    unfold lpReplicaPartialReflectProfile
    simp only [lpReplicaProfileOrbitSlotMove]
    refine ⟨by omega, he.2.2, ?_⟩
    rw [lpReplicaCurrentEdgeReflect_involutive]
    exact he.2.1
  · intro h e
    have he := h e
    rw [lpReplicaProfileOrbitSlotMove_allocation_card] at he
    unfold lpReplicaPartialReflectProfile at he
    simp only [lpReplicaProfileOrbitSlotMove] at he
    have hRle : (s.selectedRep e).card ≤ (s.allocation e).card :=
      Finset.card_le_card (s.selectedRep_subset e)
    have hR := he.2.2
    rw [lpReplicaCurrentEdgeReflect_involutive] at hR
    refine ⟨?_, hR, he.2.1⟩
    have hpe := hp e.1
    change p e.1 ≤ m e.1 at hpe
    omega


end
end StatMech.Ising
