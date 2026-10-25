/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedOrbitInjection_of_balancedHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaOffdiagBalancedHall G sites i j q) :
    LPReplicaOffdiagDecoratedOrbitInjection G sites i j q := by
  classical
  obtain ⟨move, hmove, _⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaOffdiagBalancedNeighbors G sites i j q)).mp (by
        simpa only [LPReplicaOffdiagBalancedHall] using hHall)
  exact ⟨move, hmove⟩


theorem lpReplicaOffdiagBalancedHall_of_outputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagBalancedOutputs G sites i j q).card) :
    LPReplicaOffdiagBalancedHall G sites i j q := by
  classical
  intro S
  by_cases hS : S = ∅
  · simp [hS]
  let good := lpReplicaOffdiagBalancedOutputs G sites i j q
  have hneighbors (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
      lpReplicaOffdiagBalancedNeighbors G sites i j q z = good := by
    ext y
    simp only [lpReplicaOffdiagBalancedNeighbors, good,
      lpReplicaOffdiagBalancedOutputs,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact lpReplicaOffdiagBalancedMatch_iff_output G sites i j q z y
  have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  have hunion : S.biUnion
      (lpReplicaOffdiagBalancedNeighbors G sites i j q) = good := by
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨z, hz, hy⟩
      rw [hneighbors z] at hy
      exact hy
    · intro hy
      obtain ⟨z, hz⟩ := hnonempty
      exact ⟨z, hz, by rwa [hneighbors z]⟩
  rw [hunion]
  calc
    S.card <= Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) := by
      simpa only [Finset.card_univ] using
        Finset.card_le_card (Finset.subset_univ S)
    _ <= good.card := by simpa only [good] using hcard


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagBalancedOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
  exact lpReplicaOffdiagDecoratedOrbitInjection_of_balancedHall
    G sites i j q
      (lpReplicaOffdiagBalancedHall_of_outputCard
        G sites i j q hcard)


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_balancedBranchOutputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card +
        (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard
  rwa [lpReplicaOffdiagBalancedOutputs_card_eq_branch_sum]


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_balancedProfileFiberCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : ∀ m ∈
        lpReplicaOffdiagBalancedRelevantProfiles G sites i j q,
      (lpReplicaOffdiagDecoratedSourcesAtProfile
          G sites i j q m).card <=
        (lpReplicaOffdiagBalancedLeftOutputsAtProfile
            G sites i j q m).card +
          (lpReplicaOffdiagBalancedRightOutputsAtProfile
            G sites i j q m).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_balancedBranchOutputCard
  rw [lpReplicaOffdiagDecoratedSource_card_eq_sum_profileFibers,
    lpReplicaOffdiagBalancedLeftOutputs_card_eq_sum_profileFibers,
    lpReplicaOffdiagBalancedRightOutputs_card_eq_sum_profileFibers,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hcard

end
end StatMech.Ising
