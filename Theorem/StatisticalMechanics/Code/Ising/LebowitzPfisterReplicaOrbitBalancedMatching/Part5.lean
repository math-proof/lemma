/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagBalancedOutputs_eq_branch_union
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaOffdiagBalancedOutputs G sites i j q =
      lpReplicaOffdiagBalancedBranchOutputs G sites i j q := by
  classical
  ext y
  simp only [lpReplicaOffdiagBalancedOutputs,
    lpReplicaOffdiagBalancedBranchOutputs,
    lpReplicaOffdiagBalancedLeftOutputs,
    lpReplicaOffdiagBalancedRightOutputs,
    LPReplicaOffdiagBalancedOutput, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]

theorem lpReplicaOffdiagBalancedBranchOutputs_disjoint
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Disjoint
      (lpReplicaOffdiagBalancedLeftOutputs G sites i j q)
      (lpReplicaOffdiagBalancedRightOutputs G sites i j q) := by
  classical
  rw [Finset.disjoint_left]
  intro y hyLeft hyRight
  simp only [lpReplicaOffdiagBalancedLeftOutputs,
    lpReplicaOffdiagBalancedRightOutputs, Finset.mem_filter,
    Finset.mem_univ, true_and] at hyLeft hyRight
  obtain ⟨s, rfl⟩ := hyLeft
  obtain ⟨t, ht⟩ := hyRight
  exact Sum.inl_ne_inr ht


theorem lpReplicaOffdiagBalancedOutputs_card_eq_branch_sum
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagBalancedOutputs G sites i j q).card =
      (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card +
        (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card := by
  classical
  rw [lpReplicaOffdiagBalancedOutputs_eq_branch_union]
  unfold lpReplicaOffdiagBalancedBranchOutputs
  rw [
    Finset.card_union_of_disjoint
      (lpReplicaOffdiagBalancedBranchOutputs_disjoint G sites i j q)]


end
end StatMech.Ising
