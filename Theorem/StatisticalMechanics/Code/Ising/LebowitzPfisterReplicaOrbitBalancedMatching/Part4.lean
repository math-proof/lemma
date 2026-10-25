/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedSource_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagDecoratedSourcesAtProfile
          G sites i j q m).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagDecoratedSourcesAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
    intro z hz
    unfold lpReplicaOffdiagBalancedRelevantProfiles
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))))

theorem lpReplicaOffdiagBalancedLeftOutputs_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card =
      ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagBalancedLeftOutputsAtProfile
          G sites i j q m).card := by
  classical
  simpa only [lpReplicaOffdiagBalancedLeftOutputsAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
    intro y hy
    unfold lpReplicaOffdiagBalancedRelevantProfiles
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨y, hy, rfl⟩)))))

theorem lpReplicaOffdiagBalancedRightOutputs_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card =
      ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagBalancedRightOutputsAtProfile
          G sites i j q m).card := by
  classical
  simpa only [lpReplicaOffdiagBalancedRightOutputsAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
    intro y hy
    unfold lpReplicaOffdiagBalancedRelevantProfiles
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)))


end
end StatMech.Ising
