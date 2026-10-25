/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem FiniteRankTerminalSystem.terminalClosure_eq
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) (a : A) :
    system.terminalClosure a =
      system.terminals a ∪ (system.children a).attach.biUnion
        (fun child => system.terminalClosure child.1) := by
  rw [FiniteRankTerminalSystem.terminalClosure]

theorem FiniteRankTerminalSystem.terminals_subset_terminalClosure
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) (a : A) :
    system.terminals a ⊆ system.terminalClosure a := by
  rw [system.terminalClosure_eq]
  exact Finset.subset_union_left

theorem FiniteRankTerminalSystem.terminalClosure_subset_of_mem_children
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) {a child : A}
    (hchild : child ∈ system.children a) :
    system.terminalClosure child ⊆ system.terminalClosure a := by
  intro terminal hterminal
  rw [system.terminalClosure_eq a]
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr
    ⟨⟨child, hchild⟩, Finset.mem_attach _ _, hterminal⟩


theorem FiniteRankTerminalSystem.exists_terminalEmbedding_of_hall
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B)
    (hhall : ∀ sources : Finset A,
      sources.card ≤ (sources.biUnion system.terminalClosure).card) :
    ∃ matching : A ↪ B,
      ∀ source, system.ReachesTerminal source (matching source) := by
  obtain ⟨matching, hinjective, hterminal⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      system.terminalClosure).mp hhall
  exact ⟨⟨matching, hinjective⟩, hterminal⟩


theorem exists_minimal_deficiency_one_family
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (neighborhood : Finset A -> Finset B)
    (hmono : Monotone neighborhood)
    (hfail : ∃ sources : Finset A,
      (neighborhood sources).card < sources.card) :
    ∃ sources : Finset A,
      sources.Nonempty ∧
        (neighborhood sources).card + 1 = sources.card ∧
        (∀ source ∈ sources,
          neighborhood (sources.erase source) = neighborhood sources) ∧
        ∀ smaller : Finset A, smaller ⊂ sources ->
          smaller.card ≤ (neighborhood smaller).card := by
  classical
  let bad : Finset (Finset A) := Finset.univ.filter fun sources =>
    (neighborhood sources).card < sources.card
  have hbad : bad.Nonempty := by
    obtain ⟨sources, hsources⟩ := hfail
    refine ⟨sources, ?_⟩
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨sources, hsourcesBad, hsourcesMinimal⟩ :=
    bad.exists_min_image Finset.card hbad
  have hdeficit : (neighborhood sources).card < sources.card := by
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using
      hsourcesBad
  have hsourcesNonempty : sources.Nonempty :=
    Finset.card_pos.mp (Nat.zero_lt_of_lt hdeficit)
  have hproper : ∀ smaller : Finset A, smaller ⊂ sources ->
      smaller.card ≤ (neighborhood smaller).card := by
    intro smaller hsmaller
    by_contra hnot
    have hsmallerBad : smaller ∈ bad := by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hminimal := hsourcesMinimal smaller hsmallerBad
    have hcard := Finset.card_lt_card hsmaller
    omega
  have heraseHall : ∀ source ∈ sources,
      (sources.erase source).card ≤
        (neighborhood (sources.erase source)).card := by
    intro source hsource
    exact hproper (sources.erase source)
      (Finset.erase_ssubset hsource)
  have herase : ∀ source ∈ sources,
      neighborhood (sources.erase source) = neighborhood sources := by
    intro source hsource
    have hsubset := hmono (Finset.erase_subset source sources)
    apply Finset.eq_of_subset_of_card_le hsubset
    have hhall := heraseHall source hsource
    rw [Finset.card_erase_of_mem hsource] at hhall
    omega
  have htight : (neighborhood sources).card + 1 = sources.card := by
    obtain ⟨source, hsource⟩ := hsourcesNonempty
    have hhall := heraseHall source hsource
    rw [herase source hsource, Finset.card_erase_of_mem hsource] at hhall
    omega
  exact ⟨sources, hsourcesNonempty, htight, herase, hproper⟩


end StatMech.GrahamGHS.FourColor
