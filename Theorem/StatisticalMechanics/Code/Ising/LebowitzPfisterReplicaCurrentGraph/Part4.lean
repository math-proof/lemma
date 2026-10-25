/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part4
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCurrentGraph_adj_left_right_iff
    (G : SimpleGraph V) (sites : I -> V) (x y : V) :
    (lpReplicaCurrentGraph G sites).Adj
        (.inl (.inl x)) (.inl (.inr y)) <->
      ∃ i, sites i = x ∧ sites i = y := by
  unfold lpReplicaCurrentGraph
  rw [SimpleGraph.fromRel_adj]
  simp only [lpReplicaCurrentRel]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · obtain ⟨i, hy, hx⟩ := h
      exact ⟨i, hx, hy⟩
  · intro h
    exact ⟨by simp, Or.inl h⟩


end
end StatMech.Ising
