/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part5
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCurrentSeamEdge_injective
    (sites : I -> V) (hsite : Function.Injective sites) :
    Function.Injective (lpReplicaCurrentSeamEdge sites) := by
  intro i j h
  unfold lpReplicaCurrentSeamEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · exact hsite (Sum.inl.inj (Sum.inl.inj h.1))
  · exact absurd h.1 (by simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])

theorem lpReplicaCurrentSeamEdge_mem
    (G : SimpleGraph V) (sites : I -> V) (i : I) :
    lpReplicaCurrentSeamEdge sites i ∈
      (lpReplicaCurrentGraph G sites).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  unfold lpReplicaCurrentSeamEdge
  rw [SimpleGraph.mem_edgeSet]
  unfold lpReplicaCurrentLeft lpReplicaCurrentRight
  rw [lpReplicaCurrentGraph_adj_left_right_iff]
  exact ⟨i, rfl, rfl⟩


end
end StatMech.Ising
