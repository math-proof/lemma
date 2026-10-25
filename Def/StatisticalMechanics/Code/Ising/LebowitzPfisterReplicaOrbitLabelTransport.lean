/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaProfileOrbitSlotMove
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaProfileOrbitSlotState G sites q) :
    LPReplicaProfileOrbitSlotState G sites q where
  allocation := fun e =>
    (s.allocation e \ s.selectedRep e) ∪ s.selectedReflect e
  selectedRep := s.selectedReflect
  selectedReflect := s.selectedRep
  selectedRep_subset := by
    intro e x hx
    exact Finset.mem_union_right _ hx
  selectedReflect_subset := by
    intro e x hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmove
    rw [Finset.mem_union] at hmove
    rcases hmove with hremain | hreflect
    · exact (Finset.mem_sdiff.mp hremain).2 hx
    · have hxalloc := s.selectedRep_subset e hx
      have hreflect' := s.selectedReflect_subset e hreflect
      exact (Finset.mem_sdiff.mp hreflect').2 hxalloc


end
end StatMech.Ising
