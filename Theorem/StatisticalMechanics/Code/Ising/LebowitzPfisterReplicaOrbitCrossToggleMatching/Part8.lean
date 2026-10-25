/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaOffdiagCrossToggleSelector.output_injective
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCrossToggleSelector G sites i j q) :
    Function.Injective s.output := by
  have hcross :=
    lpReplicaOrbitFourColorSlotBranchedCrossToggle_injective_of_collisionStable
      G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q)
      s.selector s.output
      (lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q) (by
        intro z w h
        exact s.collision_stable z w (congrArg Prod.fst h))
  intro z w houtput
  apply hcross
  apply Prod.ext
  · exact houtput
  · change lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (s.selector z)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (s.selector w)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w)
    rw [← s.output_state z, ← s.output_state w, houtput]


theorem nonempty_lpReplicaOffdiagCrossToggleSelector_iff_matching
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaOffdiagCrossToggleSelector G sites i j q) ↔
      Nonempty (LPReplicaOffdiagCrossToggleMatching G sites i j q) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨{
      output := s.output
      output_mem := s.output_mem
      output_injective := s.output_injective G sites i j q
      realizes := fun z => ⟨s.selector z, s.output_state z⟩
    }⟩
  · rintro ⟨m⟩
    let selector : LPReplicaOffdiagDecoratedSource G sites i j q ->
        Finset (LPReplicaOrbitCommonSlot G sites q) :=
      fun z => Classical.choose (m.realizes z)
    refine ⟨{
      selector := selector
      output := m.output
      output_mem := m.output_mem
      output_state := ?_
      collision_stable := ?_
    }⟩
    · intro z
      exact Classical.choose_spec (m.realizes z)
    · intro z w houtput
      have hzw := m.output_injective houtput
      subst w
      rfl


theorem nonempty_lpReplicaOffdiagCrossToggleMatching_iff_maskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaOffdiagCrossToggleMatching G sites i j q) ↔
      LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  classical
  constructor
  · rintro ⟨m⟩
    unfold LPReplicaOffdiagCrossToggleMaskHall
    apply (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).mpr
    refine ⟨m.output, m.output_injective, ?_⟩
    intro z
    simp only [lpReplicaOffdiagCrossToggleMaskNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and,
      LPReplicaOffdiagCrossToggleMaskRelated]
    exact ⟨m.output_mem z, m.realizes z⟩
  · intro hHall
    have hHall' : forall S : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q),
        S.card <= (S.biUnion
          (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).card := by
      simpa only [LPReplicaOffdiagCrossToggleMaskHall] using hHall
    obtain ⟨move, hmove, hmem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).mp
        hHall'
    refine ⟨{
      output := move
      output_mem := ?_
      output_injective := hmove
      realizes := ?_
    }⟩
    · intro z
      have hz := hmem z
      simp only [lpReplicaOffdiagCrossToggleMaskNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and,
        LPReplicaOffdiagCrossToggleMaskRelated] at hz
      exact hz.1
    · intro z
      have hz := hmem z
      simp only [lpReplicaOffdiagCrossToggleMaskNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and,
        LPReplicaOffdiagCrossToggleMaskRelated] at hz
      exact hz.2


theorem nonempty_lpReplicaOffdiagCrossToggleSelector_iff_maskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaOffdiagCrossToggleSelector G sites i j q) ↔
      LPReplicaOffdiagCrossToggleMaskHall G sites i j q :=
  (nonempty_lpReplicaOffdiagCrossToggleSelector_iff_matching
    G sites i j q).trans
      (nonempty_lpReplicaOffdiagCrossToggleMatching_iff_maskHall
        G sites i j q)


theorem lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCrossToggleSelector G sites i j q) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagBalancedOutputs G sites i j q).card := by
  let move : LPReplicaOffdiagDecoratedSource G sites i j q ->
      {y // y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q} :=
    fun z => ⟨s.output z, s.output_mem z⟩
  have hmove : Function.Injective move := by
    intro z w h
    apply s.output_injective G sites i j q
    exact congrArg Subtype.val h
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective move hmove


theorem lpReplicaOffdiagBalancedHall_of_crossToggleSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCrossToggleSelector G sites i j q) :
    LPReplicaOffdiagBalancedHall G sites i j q :=
  lpReplicaOffdiagBalancedHall_of_outputCard G sites i j q
    (lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector
      G sites i j q s)


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCrossToggleSelector G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard
    G sites i j q
      (lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector
        G sites i j q s)


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaOffdiagCrossToggleMaskHall G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  obtain ⟨s⟩ :=
    (nonempty_lpReplicaOffdiagCrossToggleSelector_iff_maskHall
      G sites i j q).mpr hHall
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleSelector
    G sites i j q s


theorem lpReplicaOffdiagOrbitAtomCardInequality_zero
    (G : SimpleGraph V) (sites : I -> V) (i j : I) :
    LPReplicaOffdiagOrbitAtomCardInequality
      G sites i j (fun _ => 0) :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall
    G sites i j (fun _ => 0)
      (lpReplicaOffdiagCrossToggleMaskHall_zero G sites i j)


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall
    G sites i j q
      (lpReplicaOffdiagCrossToggleMaskHall_of_commonSlotCard_le_two
        G sites hsite hij q hcard)

end
end StatMech.Ising
