/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part132
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitBranchPredicate_firstTrue_of_disjunction
    {R mainGapSum emptyGap : ℝ}
    (h :
      R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
        R ≤ mainGapSum + emptyGap) :
    unpaidRemainderReservoirSplitBranchPredicate
      (unpaidRemainderReservoirSplitBranchFirstTrue R mainGapSum emptyGap)
      R mainGapSum emptyGap := by
  by_cases hnonpos : R ≤ 0
  · simp [unpaidRemainderReservoirSplitBranchFirstTrue, hnonpos,
      unpaidRemainderReservoirSplitBranchPredicate]
  · by_cases hmain : R ≤ mainGapSum
    · simp [unpaidRemainderReservoirSplitBranchFirstTrue, hnonpos, hmain,
        unpaidRemainderReservoirSplitBranchPredicate]
    · by_cases hempty : R ≤ emptyGap
      · simp [unpaidRemainderReservoirSplitBranchFirstTrue, hnonpos, hmain,
          hempty, unpaidRemainderReservoirSplitBranchPredicate]
      · have hmixed : R ≤ mainGapSum + emptyGap := by
          rcases h with hnonpos' | hrest
          · exact False.elim (hnonpos hnonpos')
          rcases hrest with hmain' | hrest
          · exact False.elim (hmain hmain')
          rcases hrest with hempty' | hmixed
          · exact False.elim (hempty hempty')
          · exact hmixed
        simpa [unpaidRemainderReservoirSplitBranchFirstTrue, hnonpos, hmain,
          hempty, unpaidRemainderReservoirSplitBranchPredicate] using hmixed

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitBranchDisjunction_iff_le_mainEmptyGap_of_not_shortcuts
    {R mainGapSum emptyGap : ℝ}
    (hnonpos : ¬ R ≤ 0)
    (hmain : ¬ R ≤ mainGapSum)
    (hempty : ¬ R ≤ emptyGap) :
    (R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
        R ≤ mainGapSum + emptyGap) ↔
      R ≤ mainGapSum + emptyGap := by
  constructor
  · intro h
    rcases h with hnonpos' | hrest
    · exact False.elim (hnonpos hnonpos')
    rcases hrest with hmain' | hrest
    · exact False.elim (hmain hmain')
    rcases hrest with hempty' | hmixed
    · exact False.elim (hempty hempty')
    · exact hmixed
  · intro hmixed
    exact Or.inr (Or.inr (Or.inr hmixed))

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitBranchFirstTrue_eq_mixedGap_of_not_shortcuts
    {R mainGapSum emptyGap : ℝ}
    (hnonpos : ¬ R ≤ 0)
    (hmain : ¬ R ≤ mainGapSum)
    (hempty : ¬ R ≤ emptyGap) :
    unpaidRemainderReservoirSplitBranchFirstTrue R mainGapSum emptyGap =
      UnpaidRemainderReservoirSplitBranch.mixedGap := by
  simp [unpaidRemainderReservoirSplitBranchFirstTrue, hnonpos, hmain,
    hempty]

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitBranchPredicate_firstTrue_iff_le_mainEmptyGap_of_not_shortcuts
    {R mainGapSum emptyGap : ℝ}
    (hnonpos : ¬ R ≤ 0)
    (hmain : ¬ R ≤ mainGapSum)
    (hempty : ¬ R ≤ emptyGap) :
    unpaidRemainderReservoirSplitBranchPredicate
        (unpaidRemainderReservoirSplitBranchFirstTrue R mainGapSum emptyGap)
        R mainGapSum emptyGap ↔
      R ≤ mainGapSum + emptyGap := by
  rw [
    unpaidRemainderReservoirSplitBranchFirstTrue_eq_mixedGap_of_not_shortcuts
      hnonpos hmain hempty]
  rfl

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_iff_le_mainEmptyGap
    {R mainGapSum emptyGap : ℝ} :
    R - (mainGapSum + emptyGap) ≤ 0 ↔
      R ≤ mainGapSum + emptyGap := by
  constructor <;> intro h <;> linarith

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitFallbackMixedPaymentDominates_iff_le_mainEmptyGap
    {D paid mainGapSum emptyGap : ℝ} :
    D ≤ paid + mainGapSum + emptyGap ↔
      D - paid ≤ mainGapSum + emptyGap := by
  constructor <;> intro h <;> linarith

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitFallbackMixedExpandedDemand_iff_le_mainEmptyGap
    {D paid R mainGapSum emptyGap boundaryMultiplicity restoredCopy
      mainBudget emptyBudget : ℝ}
    (hR : R = D - paid)
    (hmainGap : mainGapSum = mainBudget - boundaryMultiplicity)
    (hemptyGap : emptyGap = emptyBudget - restoredCopy) :
    D + (boundaryMultiplicity + restoredCopy) ≤
        paid + (mainBudget + emptyBudget) ↔
      R ≤ mainGapSum + emptyGap := by
  constructor <;> intro h <;> linarith

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge_split
    {k : ℕ} {R boundaryMultiplicity restoredCopy mainBudget emptyBudget : ℝ}
    {demand mainCharge emptyCharge : Fin k → ℝ}
    (hR : R ≤ ∑ a : Fin k, demand a)
    (hcover : ∀ a : Fin k, demand a ≤ mainCharge a + emptyCharge a)
    (hmain :
      (∑ a : Fin k, mainCharge a) + boundaryMultiplicity ≤ mainBudget)
    (hempty :
      (∑ a : Fin k, emptyCharge a) + restoredCopy ≤ emptyBudget) :
    ∃ mainR emptyR : ℝ,
      R ≤ mainR + emptyR ∧
        mainR + boundaryMultiplicity ≤ mainBudget ∧
          emptyR + restoredCopy ≤ emptyBudget := by
  refine
    ⟨∑ a : Fin k, mainCharge a, ∑ a : Fin k, emptyCharge a, ?_,
      hmain, hempty⟩
  have hcoverSum :
      (∑ a : Fin k, demand a) ≤
        ∑ a : Fin k, (mainCharge a + emptyCharge a) :=
    Finset.sum_le_sum (fun a _ha => hcover a)
  have hsplit :
      (∑ a : Fin k, (mainCharge a + emptyCharge a)) =
        (∑ a : Fin k, mainCharge a) +
          ∑ a : Fin k, emptyCharge a := by
    rw [Finset.sum_add_distrib]
  linarith

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge_totalSlack
    {k : ℕ} {R boundaryMultiplicity restoredCopy mainBudget emptyBudget : ℝ}
    {demand mainCharge emptyCharge : Fin k → ℝ}
    (hR : R ≤ ∑ a : Fin k, demand a)
    (hcover : ∀ a : Fin k, demand a ≤ mainCharge a + emptyCharge a)
    (hmain :
      (∑ a : Fin k, mainCharge a) + boundaryMultiplicity ≤ mainBudget)
    (hempty :
      (∑ a : Fin k, emptyCharge a) + restoredCopy ≤ emptyBudget) :
    R + (boundaryMultiplicity + restoredCopy) ≤ mainBudget + emptyBudget := by
  rcases
    unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge_split
      (k := k) (R := R) (boundaryMultiplicity := boundaryMultiplicity)
      (restoredCopy := restoredCopy) (mainBudget := mainBudget)
      (emptyBudget := emptyBudget) (demand := demand)
      (mainCharge := mainCharge) (emptyCharge := emptyCharge)
      hR hcover hmain hempty with
    ⟨mainR, emptyR, hRle, hmain', hempty'⟩
  calc
    R + (boundaryMultiplicity + restoredCopy) ≤
        (mainR + emptyR) + (boundaryMultiplicity + restoredCopy) := by
      linarith
    _ = (mainR + boundaryMultiplicity) + (emptyR + restoredCopy) := by
      ring
    _ ≤ mainBudget + emptyBudget :=
      add_le_add hmain' hempty'

set_option linter.style.longLine false in


theorem finiteCharge_sum_le_sum_of_injective
    {α ρ : Type*}
    (source : Finset α) (reservoir : Finset ρ)
    (route : α → ρ) (demand : α → ℝ) (capacity : ρ → ℝ)
    (hmap : ∀ a ∈ source, route a ∈ reservoir)
    (hinj : Set.InjOn route source)
    (hcover : ∀ a ∈ source, demand a ≤ capacity (route a))
    (hcapacityNonneg : ∀ r ∈ reservoir, 0 ≤ capacity r) :
    ∑ a ∈ source, demand a ≤ ∑ r ∈ reservoir, capacity r := by
  classical
  calc
    ∑ a ∈ source, demand a ≤
        ∑ a ∈ source, capacity (route a) :=
      Finset.sum_le_sum hcover
    _ = ∑ r ∈ source.image route, capacity r := by
      rw [Finset.sum_image (fun a ha b hb => hinj ha hb)]
    _ ≤ ∑ r ∈ reservoir, capacity r := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
      · intro r hr
        rw [Finset.mem_image] at hr
        rcases hr with ⟨a, ha, rfl⟩
        exact hmap a ha
      · intro r hr _hnot
        exact hcapacityNonneg r hr

set_option linter.style.longLine false in


theorem finiteHallSubtypeSelector
    {Atom Slot : Type*}
    (atoms : Finset Atom)
    (candidateSlots : Atom → Finset Slot)
    (hHall :
      ∀ S : Finset Atom, S ⊆ atoms →
        S.card ≤
          (@Finset.biUnion Atom Slot (Classical.decEq Slot)
            S candidateSlots).card) :
    ∃ route : {a // a ∈ atoms} → Slot,
      Function.Injective route ∧
        ∀ a : {a // a ∈ atoms}, route a ∈ candidateSlots a.1 := by
  classical
  set t : {a // a ∈ atoms} → Finset Slot :=
    fun a => candidateSlots a.1 with ht
  have hHallSub :
      ∀ s : Finset {a // a ∈ atoms}, s.card ≤ (s.biUnion t).card := by
    intro s
    set S : Finset Atom := s.image (fun a => a.1) with hS
    have hSsub : S ⊆ atoms := by
      intro a ha
      rw [hS, Finset.mem_image] at ha
      rcases ha with ⟨a', _ha', rfl⟩
      exact a'.2
    have hcardS : S.card = s.card := by
      rw [hS, Finset.card_image_of_injective]
      exact fun a b hab => Subtype.ext hab
    have hbiUnion : s.biUnion t = S.biUnion candidateSlots := by
      ext slot
      simp only [Finset.mem_biUnion, ht, hS, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, hslot⟩
        exact ⟨a.1, ⟨a, ha, rfl⟩, hslot⟩
      · rintro ⟨a, ⟨a', ha', rfl⟩, hslot⟩
        exact ⟨a', ha', hslot⟩
    rw [← hcardS, hbiUnion]
    exact hHall S hSsub
  rcases
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHallSub with
    ⟨route, hrouteInjective, hrouteMem⟩
  exact ⟨route, hrouteInjective, hrouteMem⟩

set_option linter.style.longLine false in


theorem finiteHallCondition_of_pairwiseDisjoint_nonempty
    {Atom Slot : Type*}
    (atoms : Finset Atom)
    (candidateSlots : Atom → Finset Slot)
    (hne : ∀ a, a ∈ atoms → (candidateSlots a).Nonempty)
    (hdisj :
      ∀ a, a ∈ atoms → ∀ b, b ∈ atoms → a ≠ b →
        Disjoint (candidateSlots a) (candidateSlots b)) :
    ∀ S : Finset Atom, S ⊆ atoms →
      S.card ≤
        (@Finset.biUnion Atom Slot (Classical.decEq Slot)
          S candidateSlots).card := by
  classical
  intro S hS
  rw [Finset.card_biUnion
    (fun a ha b hb hab => hdisj a (hS ha) b (hS hb) hab)]
  calc
    S.card = ∑ _a ∈ S, 1 := by
      rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ a ∈ S, (candidateSlots a).card :=
      Finset.sum_le_sum
        (fun a ha => Finset.Nonempty.card_pos (hne a (hS ha)))

set_option linter.style.longLine false in


theorem finiteHallCondition_of_capacityScalarDisjoint_nonempty
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (hne :
      ∀ a, a ∈ atoms →
        (∃ d, d ∈ mainSlots ∧ demand a ≤ mainCap d) ∨
          demand a ≤ emptyCap)
    (hdisj :
      ∀ a, a ∈ atoms → ∀ b, b ∈ atoms → a ≠ b →
        (∀ d, d ∈ mainSlots →
          ¬ (demand a ≤ mainCap d ∧ demand b ≤ mainCap d)) ∧
          ¬ (demand a ≤ emptyCap ∧ demand b ≤ emptyCap)) :
    ∀ S : Finset Atom, S ⊆ atoms →
      S.card ≤
        (@Finset.biUnion Atom (Sum MainSlot Unit)
          (Classical.decEq (Sum MainSlot Unit))
          S
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand)).card := by
  classical
  refine
    finiteHallCondition_of_pairwiseDisjoint_nonempty
      (atoms := atoms)
      (candidateSlots :=
        canonicalCapacityCandidateSlots
          mainSlots mainCap emptyCap demand)
      ?_ ?_
  · intro a ha
    rw [canonicalCapacityCandidateSlots_nonempty_iff]
    exact hne a ha
  · intro a ha b hb hab
    rw [canonicalCapacityCandidateSlots_disjoint_iff]
    exact hdisj a ha b hb hab

set_option linter.style.longLine false in


theorem finiteHallCondition_of_capacityScalarMaxDisjoint_nonempty
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (hne :
      ∀ a, a ∈ atoms →
        (∃ d, d ∈ mainSlots ∧ demand a ≤ mainCap d) ∨
          demand a ≤ emptyCap)
    (hdisj :
      ∀ a, a ∈ atoms → ∀ b, b ∈ atoms → a ≠ b →
        (∀ d, d ∈ mainSlots →
          mainCap d < max (demand a) (demand b)) ∧
          emptyCap < max (demand a) (demand b)) :
    ∀ S : Finset Atom, S ⊆ atoms →
      S.card ≤
        (@Finset.biUnion Atom (Sum MainSlot Unit)
          (Classical.decEq (Sum MainSlot Unit))
          S
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand)).card := by
  classical
  exact
    finiteHallCondition_of_capacityScalarDisjoint_nonempty
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) hne
      (hdisj := by
        intro a ha b hb hab
        have hstrict := hdisj a ha b hb hab
        constructor
        · intro d hd
          exact
            (not_both_le_iff_lt_max
              (x := demand a) (y := demand b) (c := mainCap d)).mpr
              (hstrict.1 d hd)
        · exact
            (not_both_le_iff_lt_max
              (x := demand a) (y := demand b) (c := emptyCap)).mpr
              hstrict.2)

set_option linter.style.longLine false in


theorem finiteHallCondition_of_capacityThresholdCounts
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (hThreshold :
      ∀ a, a ∈ atoms →
        (atoms.filter (fun b => demand a ≤ demand b)).card ≤
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand a).card) :
    ∀ S : Finset Atom, S ⊆ atoms →
      S.card ≤
        (@Finset.biUnion Atom (Sum MainSlot Unit)
          (Classical.decEq (Sum MainSlot Unit))
          S
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand)).card := by
  classical
  intro S hS
  by_cases hSne : S.Nonempty
  · rcases Finset.exists_min_image S demand hSne with
      ⟨a0, ha0S, hmin⟩
    have ha0Atoms : a0 ∈ atoms := hS ha0S
    have hSsubThreshold :
        S ⊆ atoms.filter (fun b => demand a0 ≤ demand b) := by
      intro b hb
      exact Finset.mem_filter.mpr ⟨hS hb, hmin b hb⟩
    have hCandSubset :
        canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand a0 ⊆
          @Finset.biUnion Atom (Sum MainSlot Unit)
            (Classical.decEq (Sum MainSlot Unit))
            S
            (canonicalCapacityCandidateSlots
              mainSlots mainCap emptyCap demand) := by
      intro slot hslot
      simpa [Finset.mem_biUnion] using ⟨a0, ha0S, hslot⟩
    exact
      le_trans (Finset.card_le_card hSsubThreshold)
        (le_trans (hThreshold a0 ha0Atoms)
          (Finset.card_le_card hCandSubset))
  · rw [Finset.not_nonempty_iff_eq_empty] at hSne
    simp [hSne]

set_option linter.style.longLine false in


theorem finiteHallCondition_capacityThresholdCounts_iff
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ) :
    (∀ S : Finset Atom, S ⊆ atoms →
      S.card ≤
        (@Finset.biUnion Atom (Sum MainSlot Unit)
          (Classical.decEq (Sum MainSlot Unit))
          S
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand)).card) ↔
      ∀ a, a ∈ atoms →
        (atoms.filter (fun b => demand a ≤ demand b)).card ≤
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand a).card := by
  constructor
  · intro hHall a ha
    have hTailSub :
        atoms.filter (fun b => demand a ≤ demand b) ⊆ atoms :=
      Finset.filter_subset _ _
    have hTail :=
      hHall (atoms.filter (fun b => demand a ≤ demand b)) hTailSub
    have hUnion :=
      canonicalCapacityCandidateSlots_biUnion_thresholdTail_eq
        (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) ha
    simpa [hUnion] using hTail
  · intro hThreshold
    exact
      finiteHallCondition_of_capacityThresholdCounts
        (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) hThreshold

set_option linter.style.longLine false in


theorem finiteHallCondition_of_capacityThresholdScalarCounts
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (hThreshold :
      ∀ a, a ∈ atoms →
        (atoms.filter (fun b => demand a ≤ demand b)).card ≤
          (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
            if demand a ≤ emptyCap then 1 else 0) :
    ∀ S : Finset Atom, S ⊆ atoms →
      S.card ≤
        (@Finset.biUnion Atom (Sum MainSlot Unit)
          (Classical.decEq (Sum MainSlot Unit))
          S
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand)).card := by
  classical
  exact
    finiteHallCondition_of_capacityThresholdCounts
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand)
      (hThreshold := by
        intro a ha
        calc
          (atoms.filter (fun b => demand a ≤ demand b)).card ≤
              (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
                if demand a ≤ emptyCap then 1 else 0 :=
            hThreshold a ha
          _ =
              (canonicalCapacityCandidateSlots
                mainSlots mainCap emptyCap demand a).card := by
            exact
              (canonicalCapacityCandidateSlots_card
                (mainSlots := mainSlots) (mainCap := mainCap)
                (emptyCap := emptyCap) (demand := demand) (a := a)).symm)

set_option linter.style.longLine false in


theorem finiteHallCondition_capacityThresholdScalarCounts_iff
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ) :
    (∀ S : Finset Atom, S ⊆ atoms →
      S.card ≤
        (@Finset.biUnion Atom (Sum MainSlot Unit)
          (Classical.decEq (Sum MainSlot Unit))
          S
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand)).card) ↔
      ∀ a, a ∈ atoms →
        (atoms.filter (fun b => demand a ≤ demand b)).card ≤
          (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
            if demand a ≤ emptyCap then 1 else 0 := by
  constructor
  · intro hHall a ha
    have hCandidate :
        (atoms.filter (fun b => demand a ≤ demand b)).card ≤
          (canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand a).card :=
      (finiteHallCondition_capacityThresholdCounts_iff
        (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand)).mp hHall a ha
    simpa [canonicalCapacityCandidateSlots_card
      (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) (a := a)] using hCandidate
  · intro hThreshold
    exact
      finiteHallCondition_of_capacityThresholdScalarCounts
        (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) hThreshold

set_option linter.style.longLine false in


theorem finiteHall_exists_injOn_of_hall_with_default
    {Atom Slot : Type*}
    (atoms : Finset Atom)
    (candidateSlots : Atom → Finset Slot)
    (defaultSlot : Slot)
    (hHall :
      ∀ S : Finset Atom, S ⊆ atoms →
        S.card ≤
          (@Finset.biUnion Atom Slot (Classical.decEq Slot)
            S candidateSlots).card) :
    ∃ route : Atom → Slot,
      (∀ a, a ∈ atoms → route a ∈ candidateSlots a) ∧
        Set.InjOn route atoms := by
  classical
  rcases finiteHallSubtypeSelector atoms candidateSlots hHall with
    ⟨subroute, hsubrouteInjective, hsubrouteMem⟩
  let routeFn : Atom → Slot :=
    fun a => if ha : a ∈ atoms then subroute ⟨a, ha⟩ else defaultSlot
  refine ⟨routeFn, ?_, ?_⟩
  · intro a ha
    dsimp [routeFn]
    rw [dif_pos ha]
    exact hsubrouteMem ⟨a, ha⟩
  · intro a ha b hb hroute
    have haFin : a ∈ atoms := by
      simpa using ha
    have hbFin : b ∈ atoms := by
      simpa using hb
    have hroute' : subroute ⟨a, haFin⟩ = subroute ⟨b, hbFin⟩ := by
      dsimp [routeFn] at hroute
      rw [dif_pos haFin, dif_pos hbFin] at hroute
      exact hroute
    exact congrArg Subtype.val (hsubrouteInjective hroute')

set_option linter.style.longLine false in


theorem canonicalCapacityGlobalRouteInjOn_of_capacityScalarDisjoint_nonempty
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (hne :
      ∀ a, a ∈ atoms →
        (∃ d, d ∈ mainSlots ∧ demand a ≤ mainCap d) ∨
          demand a ≤ emptyCap)
    (hdisj :
      ∀ a, a ∈ atoms → ∀ b, b ∈ atoms → a ≠ b →
        (∀ d, d ∈ mainSlots →
          ¬ (demand a ≤ mainCap d ∧ demand b ≤ mainCap d)) ∧
          ¬ (demand a ≤ emptyCap ∧ demand b ≤ emptyCap)) :
    ∃ route : Atom → Sum MainSlot Unit,
      (∀ a, a ∈ atoms →
        match route a with
        | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
        | Sum.inr _ => demand a ≤ emptyCap) ∧
        Set.InjOn route atoms := by
  classical
  let candidateSlots : Atom → Finset (Sum MainSlot Unit) :=
    canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand
  have hHall :
      ∀ S : Finset Atom, S ⊆ atoms →
        S.card ≤
          (@Finset.biUnion Atom (Sum MainSlot Unit)
            (Classical.decEq (Sum MainSlot Unit))
            S candidateSlots).card := by
    simpa [candidateSlots] using
      finiteHallCondition_of_capacityScalarDisjoint_nonempty
        (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) hne hdisj
  rcases
    finiteHall_exists_injOn_of_hall_with_default
      (atoms := atoms) (candidateSlots := candidateSlots)
      (defaultSlot := (Sum.inr () : Sum MainSlot Unit)) hHall with
    ⟨route, hrouteMem, hinj⟩
  refine ⟨route, ?_, hinj⟩
  intro a ha
  have hmem :
      route a ∈
        canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
    simpa [candidateSlots] using hrouteMem a ha
  cases hslot : route a with
  | inl d =>
      have hmem' :
          Sum.inl d ∈
            canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
        simpa [hslot] using hmem
      simpa [hslot] using
        canonicalCapacityCandidateSlots_mem_compatible
          (mainSlots := mainSlots) (mainCap := mainCap)
          (emptyCap := emptyCap) (demand := demand) (a := a)
          (slot := Sum.inl d) hmem'
  | inr u =>
      have hmem' :
          Sum.inr u ∈
            canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
        simpa [hslot] using hmem
      simpa [hslot] using
        canonicalCapacityCandidateSlots_mem_compatible
          (mainSlots := mainSlots) (mainCap := mainCap)
          (emptyCap := emptyCap) (demand := demand) (a := a)
          (slot := Sum.inr u) hmem'

set_option linter.style.longLine false in


theorem canonicalCapacityGlobalRouteInjOn_of_capacityScalarMaxDisjoint_nonempty
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (hne :
      ∀ a, a ∈ atoms →
        (∃ d, d ∈ mainSlots ∧ demand a ≤ mainCap d) ∨
          demand a ≤ emptyCap)
    (hdisj :
      ∀ a, a ∈ atoms → ∀ b, b ∈ atoms → a ≠ b →
        (∀ d, d ∈ mainSlots →
          mainCap d < max (demand a) (demand b)) ∧
          emptyCap < max (demand a) (demand b)) :
    ∃ route : Atom → Sum MainSlot Unit,
      (∀ a, a ∈ atoms →
        match route a with
        | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
        | Sum.inr _ => demand a ≤ emptyCap) ∧
        Set.InjOn route atoms := by
  classical
  exact
    canonicalCapacityGlobalRouteInjOn_of_capacityScalarDisjoint_nonempty
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) hne
      (hdisj := by
        intro a ha b hb hab
        have hstrict := hdisj a ha b hb hab
        constructor
        · intro d hd
          exact
            (not_both_le_iff_lt_max
              (x := demand a) (y := demand b) (c := mainCap d)).mpr
              (hstrict.1 d hd)
        · exact
            (not_both_le_iff_lt_max
              (x := demand a) (y := demand b) (c := emptyCap)).mpr
              hstrict.2)

set_option linter.style.longLine false in


theorem canonicalCapacityGlobalRouteInjOn_of_thresholdScalarCount
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (hThreshold :
      ∀ a, a ∈ atoms →
        (atoms.filter (fun b => demand a ≤ demand b)).card ≤
          (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
            if demand a ≤ emptyCap then 1 else 0) :
    ∃ route : Atom → Sum MainSlot Unit,
      (∀ a, a ∈ atoms →
        match route a with
        | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
        | Sum.inr _ => demand a ≤ emptyCap) ∧
        Set.InjOn route atoms := by
  classical
  let candidateSlots : Atom → Finset (Sum MainSlot Unit) :=
    canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand
  have hHall :
      ∀ S : Finset Atom, S ⊆ atoms →
        S.card ≤
          (@Finset.biUnion Atom (Sum MainSlot Unit)
            (Classical.decEq (Sum MainSlot Unit))
            S candidateSlots).card := by
    simpa [candidateSlots] using
      finiteHallCondition_of_capacityThresholdScalarCounts
        (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) hThreshold
  rcases
    finiteHall_exists_injOn_of_hall_with_default
      (atoms := atoms) (candidateSlots := candidateSlots)
      (defaultSlot := (Sum.inr () : Sum MainSlot Unit)) hHall with
    ⟨route, hrouteMem, hinj⟩
  refine ⟨route, ?_, hinj⟩
  intro a ha
  have hmem :
      route a ∈
        canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
    simpa [candidateSlots] using hrouteMem a ha
  cases hslot : route a with
  | inl d =>
      have hmem' :
          Sum.inl d ∈
            canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
        simpa [hslot] using hmem
      simpa [hslot] using
        canonicalCapacityCandidateSlots_mem_compatible
          (mainSlots := mainSlots) (mainCap := mainCap)
          (emptyCap := emptyCap) (demand := demand) (a := a)
          (slot := Sum.inl d) hmem'
  | inr u =>
      have hmem' :
          Sum.inr u ∈
            canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
        simpa [hslot] using hmem
      simpa [hslot] using
        canonicalCapacityCandidateSlots_mem_compatible
          (mainSlots := mainSlots) (mainCap := mainCap)
          (emptyCap := emptyCap) (demand := demand) (a := a)
          (slot := Sum.inr u) hmem'

set_option linter.style.longLine false in


theorem canonicalCapacityGlobalRouteInjOn_iff_thresholdScalarCount
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ) :
    (∃ route : Atom → Sum MainSlot Unit,
      (∀ a, a ∈ atoms →
        match route a with
        | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
        | Sum.inr _ => demand a ≤ emptyCap) ∧
        Set.InjOn route atoms) ↔
      ∀ a, a ∈ atoms →
        (atoms.filter (fun b => demand a ≤ demand b)).card ≤
          (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
            if demand a ≤ emptyCap then 1 else 0 := by
  constructor
  · rintro ⟨route, hroute, hinj⟩
    exact
      canonicalCapacityThresholdScalarCount_of_globalRouteInjOn
        (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) (route := route)
        hroute hinj
  · intro hThreshold
    exact
      canonicalCapacityGlobalRouteInjOn_of_thresholdScalarCount
        (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) hThreshold

set_option linter.style.longLine false in


theorem canonicalCapacityThresholdScalarCount_of_rankedPrefixCapacityProfile
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (slotAt : Fin atoms.card → Sum MainSlot Unit)
    (hslotMem :
      ∀ i,
        match slotAt i with
        | Sum.inl d => d ∈ mainSlots
        | Sum.inr _ => True)
    (hslotInj : Function.Injective slotAt)
    (hslotCapacity :
      ∀ a, a ∈ atoms →
        ∀ i : Fin atoms.card,
          (i : ℕ) < (atoms.filter (fun b => demand a ≤ demand b)).card →
            match slotAt i with
            | Sum.inl d => demand a ≤ mainCap d
            | Sum.inr _ => demand a ≤ emptyCap) :
    ∀ a, a ∈ atoms →
      (atoms.filter (fun b => demand a ≤ demand b)).card ≤
        (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
          if demand a ≤ emptyCap then 1 else 0 := by
  classical
  intro a ha
  let tail := atoms.filter (fun b => demand a ≤ demand b)
  have htailSubset : tail ⊆ atoms := Finset.filter_subset _ _
  have htailCardLe : tail.card ≤ atoms.card :=
    Finset.card_le_card htailSubset
  let candidate :=
    canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a
  have hprefix :
      ∀ i : Fin atoms.card, (i : ℕ) < tail.card → slotAt i ∈ candidate := by
    intro i hi
    have hiTail :
        (i : ℕ) < (atoms.filter (fun b => demand a ≤ demand b)).card := by
      simpa [tail] using hi
    have hcap := hslotCapacity a ha i hiTail
    have hmem := hslotMem i
    cases hslot : slotAt i with
    | inl d =>
        have hcompat : d ∈ mainSlots ∧ demand a ≤ mainCap d := by
          exact
            ⟨by simpa [hslot] using hmem,
              by simpa [hslot] using hcap⟩
        have hslotCandidate :
            Sum.inl d ∈
              canonicalCapacityCandidateSlots
                mainSlots mainCap emptyCap demand a :=
          canonicalCapacityCandidateSlots_mem_of_compatible
            (mainSlots := mainSlots) (mainCap := mainCap)
            (emptyCap := emptyCap) (demand := demand) (a := a)
            (slot := Sum.inl d) hcompat
        simpa [candidate, hslot] using hslotCandidate
    | inr u =>
        have hcompat : demand a ≤ emptyCap := by
          simpa [hslot] using hcap
        have hslotCandidate :
            Sum.inr u ∈
              canonicalCapacityCandidateSlots
                mainSlots mainCap emptyCap demand a :=
          canonicalCapacityCandidateSlots_mem_of_compatible
            (mainSlots := mainSlots) (mainCap := mainCap)
            (emptyCap := emptyCap) (demand := demand) (a := a)
            (slot := Sum.inr u) hcompat
        simpa [candidate, hslot] using hslotCandidate
  have htailLeCandidate : tail.card ≤ candidate.card := by
    exact
      card_le_card_of_injective_rankedPrefix
        (target := candidate) (slotAt := slotAt) (k := tail.card)
        htailCardLe hslotInj hprefix
  calc
    (atoms.filter (fun b => demand a ≤ demand b)).card = tail.card := rfl
    _ ≤ candidate.card := htailLeCandidate
    _ =
        (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
          if demand a ≤ emptyCap then 1 else 0 := by
        simpa [candidate] using
          canonicalCapacityCandidateSlots_card
            (mainSlots := mainSlots) (mainCap := mainCap)
            (emptyCap := emptyCap) (demand := demand) (a := a)

set_option linter.style.longLine false in


theorem canonicalCapacityRankedPrefixCapacityProfile_of_sortedAtomSlotCapacityProfile
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (atomAt : Fin atoms.card → Atom)
    (slotAt : Fin atoms.card → Sum MainSlot Unit)
    (hatomSurj : ∀ a, a ∈ atoms → ∃ i, atomAt i = a)
    (hatomSorted : ∀ i j : Fin atoms.card, (i : ℕ) ≤ (j : ℕ) →
      demand (atomAt j) ≤ demand (atomAt i))
    (hslotCapacitySelf :
      ∀ i,
        match slotAt i with
        | Sum.inl d => demand (atomAt i) ≤ mainCap d
        | Sum.inr _ => demand (atomAt i) ≤ emptyCap) :
    ∀ a, a ∈ atoms →
      ∀ i : Fin atoms.card,
        (i : ℕ) < (atoms.filter (fun b => demand a ≤ demand b)).card →
          match slotAt i with
          | Sum.inl d => demand a ≤ mainCap d
          | Sum.inr _ => demand a ≤ emptyCap := by
  intro a _ha i hi
  have hthreshold : demand a ≤ demand (atomAt i) :=
    sortedEnumeration_mem_thresholdTail_of_lt_filter_card
      (s := atoms) (score := demand) (itemAt := atomAt)
      (hitemSurj := hatomSurj) (hitemSorted := hatomSorted)
      (threshold := demand a) i hi
  have hself := hslotCapacitySelf i
  cases hslot : slotAt i with
  | inl d =>
      have hself' : demand (atomAt i) ≤ mainCap d := by
        simpa [hslot] using hself
      exact hthreshold.trans hself'
  | inr u =>
      have hself' : demand (atomAt i) ≤ emptyCap := by
        simpa [hslot] using hself
      exact hthreshold.trans hself'

set_option linter.style.longLine false in


theorem canonicalCapacityThresholdScalarCount_of_sortedAtomSlotCapacityProfile
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (atomAt : Fin atoms.card → Atom)
    (slotAt : Fin atoms.card → Sum MainSlot Unit)
    (hatomSurj : ∀ a, a ∈ atoms → ∃ i, atomAt i = a)
    (hatomSorted : ∀ i j : Fin atoms.card, (i : ℕ) ≤ (j : ℕ) →
      demand (atomAt j) ≤ demand (atomAt i))
    (hslotMem :
      ∀ i,
        match slotAt i with
        | Sum.inl d => d ∈ mainSlots
        | Sum.inr _ => True)
    (hslotInj : Function.Injective slotAt)
    (hslotCapacitySelf :
      ∀ i,
        match slotAt i with
        | Sum.inl d => demand (atomAt i) ≤ mainCap d
        | Sum.inr _ => demand (atomAt i) ≤ emptyCap) :
    ∀ a, a ∈ atoms →
      (atoms.filter (fun b => demand a ≤ demand b)).card ≤
        (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
          if demand a ≤ emptyCap then 1 else 0 := by
  classical
  apply
    canonicalCapacityThresholdScalarCount_of_rankedPrefixCapacityProfile
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) (slotAt := slotAt)
      (hslotMem := hslotMem) (hslotInj := hslotInj)
      (hslotCapacity :=
        canonicalCapacityRankedPrefixCapacityProfile_of_sortedAtomSlotCapacityProfile
          (atoms := atoms) (mainCap := mainCap) (emptyCap := emptyCap)
          (demand := demand) (atomAt := atomAt) (slotAt := slotAt)
          hatomSurj hatomSorted hslotCapacitySelf)

set_option linter.style.longLine false in


theorem canonicalCapacitySortedAtomSlotProfile_of_globalRouteInjOn
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (route : Atom → Sum MainSlot Unit)
    (hroute :
      ∀ a, a ∈ atoms →
        match route a with
        | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
        | Sum.inr _ => demand a ≤ emptyCap)
    (hinj : Set.InjOn route atoms) :
    ∃ atomAt : Fin atoms.card → Atom,
      ∃ slotAt : Fin atoms.card → Sum MainSlot Unit,
        (∀ i, atomAt i ∈ atoms) ∧
          Function.Injective atomAt ∧
            (∀ a, a ∈ atoms → ∃ i, atomAt i = a) ∧
              (∀ i j : Fin atoms.card, (i : ℕ) ≤ (j : ℕ) →
                demand (atomAt j) ≤ demand (atomAt i)) ∧
                (∀ i,
                  match slotAt i with
                  | Sum.inl d => d ∈ mainSlots
                  | Sum.inr _ => True) ∧
                  Function.Injective slotAt ∧
                    (∀ i,
                      match slotAt i with
                      | Sum.inl d => demand (atomAt i) ≤ mainCap d
                      | Sum.inr _ => demand (atomAt i) ≤ emptyCap) := by
  classical
  rcases exists_sortedFinsetEnumeration atoms demand with
    ⟨atomAt, hatomMem, hatomInj, hatomSurj, hatomSorted⟩
  let slotAt : Fin atoms.card → Sum MainSlot Unit := fun i => route (atomAt i)
  refine ⟨atomAt, slotAt, hatomMem, hatomInj, hatomSurj, hatomSorted,
    ?_, ?_, ?_⟩
  · intro i
    have hroute' := hroute (atomAt i) (hatomMem i)
    cases hslot : route (atomAt i) with
    | inl d =>
        have hmain : d ∈ mainSlots ∧ demand (atomAt i) ≤ mainCap d := by
          simpa [hslot] using hroute'
        simpa [slotAt, hslot] using hmain.1
    | inr u =>
        simp [slotAt, hslot]
  · intro i j hij
    apply hatomInj
    exact hinj (hatomMem i) (hatomMem j) hij
  · intro i
    have hroute' := hroute (atomAt i) (hatomMem i)
    cases hslot : route (atomAt i) with
    | inl d =>
        have hmain : d ∈ mainSlots ∧ demand (atomAt i) ≤ mainCap d := by
          simpa [hslot] using hroute'
        simpa [slotAt, hslot] using hmain.2
    | inr u =>
        simpa [slotAt, hslot] using hroute'

set_option linter.style.longLine false in


theorem canonicalCapacitySortedAtomSlotProfile_of_thresholdScalarCount
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (hThreshold :
      ∀ a, a ∈ atoms →
        (atoms.filter (fun b => demand a ≤ demand b)).card ≤
          (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
            if demand a ≤ emptyCap then 1 else 0) :
    ∃ atomAt : Fin atoms.card → Atom,
      ∃ slotAt : Fin atoms.card → Sum MainSlot Unit,
        (∀ i, atomAt i ∈ atoms) ∧
          Function.Injective atomAt ∧
            (∀ a, a ∈ atoms → ∃ i, atomAt i = a) ∧
              (∀ i j : Fin atoms.card, (i : ℕ) ≤ (j : ℕ) →
                demand (atomAt j) ≤ demand (atomAt i)) ∧
                (∀ i,
                  match slotAt i with
                  | Sum.inl d => d ∈ mainSlots
                  | Sum.inr _ => True) ∧
                  Function.Injective slotAt ∧
                    (∀ i,
                      match slotAt i with
                      | Sum.inl d => demand (atomAt i) ≤ mainCap d
                      | Sum.inr _ => demand (atomAt i) ≤ emptyCap) := by
  classical
  rcases
    canonicalCapacityGlobalRouteInjOn_of_thresholdScalarCount
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) hThreshold with
    ⟨route, hroute, hinj⟩
  exact
    canonicalCapacitySortedAtomSlotProfile_of_globalRouteInjOn
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) (route := route)
      hroute hinj

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          ∃ atomAt : Fin atoms.card → Atom,
            ∃ slotAt :
                Fin atoms.card →
                  Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v)
                    Unit,
              (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                R ≤ ∑ a ∈ atoms, demand a ∧
                  (∀ i, atomAt i ∈ atoms) ∧
                    Function.Injective atomAt ∧
                      (∀ a, a ∈ atoms → ∃ i, atomAt i = a) ∧
                        (∀ i j : Fin atoms.card, (i : ℕ) ≤ (j : ℕ) →
                          demand (atomAt j) ≤ demand (atomAt i)) ∧
                          (∀ i,
                            match slotAt i with
                            | Sum.inl d => d ∈ I.image
                            | Sum.inr _ => True) ∧
                            Function.Injective slotAt ∧
                              (∀ i,
                                match slotAt i with
                                | Sum.inl d =>
                                    demand (atomAt i) ≤ mainGap d
                                | Sum.inr _ =>
                                    demand (atomAt i) ≤ emptyGap)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, route, hdemandNonneg, hRle, hrouteMem,
      hrouteInj, hrouteCapacity⟩
  rcases
    canonicalCapacitySortedAtomSlotProfile_of_globalRouteInjOn
      (atoms := atoms) (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand) (route := route)
      (hroute := by
        intro a ha
        have hmem := hrouteMem a ha
        have hcap := hrouteCapacity a ha
        cases hslot : route a with
        | inl d =>
            have hmem' : d ∈ I.image := by
              simpa [hslot] using hmem
            have hcap' : demand a ≤ mainGap d := by
              simpa [mainGap, emptyGap, hslot] using hcap
            exact ⟨hmem', hcap'⟩
        | inr u =>
            simpa [mainGap, emptyGap, hslot] using hcap)
      (hinj := hrouteInj) with
    ⟨atomAt, slotAt, hatomMem, hatomInj, hatomSurj, hatomSorted,
      hslotMem, hslotInj, hslotCapacitySelf⟩
  refine ⟨Atom, atoms, demand, atomAt, slotAt, hdemandNonneg, hRle,
    hatomMem, hatomInj, hatomSurj, hatomSorted, ?_, hslotInj, ?_⟩
  · intro i
    have hmem := hslotMem i
    cases hslot : slotAt i with
    | inl d =>
        simpa [hslot] using hmem
    | inr u =>
        trivial
  · intro i
    have hcap := hslotCapacitySelf i
    cases hslot : slotAt i with
    | inl d =>
        simpa [mainGap, emptyGap, hslot] using hcap
    | inr u =>
        simpa [mainGap, emptyGap, hslot] using hcap

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          ∃ slotAt :
              Fin atoms.card →
                Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit,
            (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
              R ≤ ∑ a ∈ atoms, demand a ∧
                (∀ i,
                  match slotAt i with
                  | Sum.inl d => d ∈ I.image
                  | Sum.inr _ => True) ∧
                  Function.Injective slotAt ∧
                    (∀ a, a ∈ atoms →
                      ∀ i : Fin atoms.card,
                        (i : ℕ) <
                            (atoms.filter
                              (fun b => demand a ≤ demand b)).card →
                          match slotAt i with
                          | Sum.inl d => demand a ≤ mainGap d
                          | Sum.inr _ => demand a ≤ emptyGap)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, atomAt, slotAt, hdemandNonneg, hRle,
      _hatomMem, _hatomInj, hatomSurj, hatomSorted, hslotMem, hslotInj,
      hslotCapacitySelf⟩
  refine ⟨Atom, atoms, demand, slotAt, hdemandNonneg, hRle,
    hslotMem, hslotInj, ?_⟩
  intro a _ha i hi
  have hthreshold : demand a ≤ demand (atomAt i) :=
    sortedEnumeration_mem_thresholdTail_of_lt_filter_card
      (s := atoms) (score := demand) (itemAt := atomAt)
      (hitemSurj := hatomSurj) (hitemSorted := hatomSorted)
      (threshold := demand a) i hi
  have hself := hslotCapacitySelf i
  cases hslot : slotAt i with
  | inl d =>
      have hself' : demand (atomAt i) ≤ mainGap d := by
        simpa [mainGap, Ωnz, emptyGap, hslot] using hself
      exact hthreshold.trans hself'
  | inr u =>
      have hself' : demand (atomAt i) ≤ emptyGap := by
        simpa [mainGap, Ωnz, emptyGap, hslot] using hself
      exact hthreshold.trans hself'

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
            R ≤ ∑ a ∈ atoms, demand a ∧
              (∀ a, a ∈ atoms →
                (atoms.filter (fun b => demand a ≤ demand b)).card ≤
                  (I.image.filter (fun d => demand a ≤ mainGap d)).card +
                    if demand a ≤ emptyGap then 1 else 0)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, slotAt, hdemandNonneg, hRle, hslotMem,
      hslotInj, hslotCapacity⟩
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  exact
    canonicalCapacityThresholdScalarCount_of_rankedPrefixCapacityProfile
      (atoms := atoms) (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand) (slotAt := slotAt)
      (hslotMem := by
        intro i
        have hmem := hslotMem i
        cases hslot : slotAt i with
        | inl d =>
            simpa [hslot] using hmem
        | inr u =>
            trivial)
      (hslotInj := hslotInj)
      (hslotCapacity := by
        intro a ha i hi
        have hcap := hslotCapacity a ha i hi
        cases hslot : slotAt i with
        | inl d =>
            simpa [hslot] using hcap
        | inr u =>
            simpa [hslot] using hcap)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          ∃ route :
              Atom →
                Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit,
            (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
              R ≤ ∑ a ∈ atoms, demand a ∧
                (∀ a, a ∈ atoms →
                  match route a with
                  | Sum.inl d => d ∈ I.image
                  | Sum.inr _ => True) ∧
                  Set.InjOn route atoms ∧
                    (∀ a, a ∈ atoms →
                      demand a ≤
                        match route a with
                        | Sum.inl d => mainGap d
                        | Sum.inr _ => emptyGap)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hThreshold⟩
  rcases
    canonicalCapacityGlobalRouteInjOn_of_thresholdScalarCount
      (atoms := atoms) (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand)
      (by
        intro a ha
        simpa [I, mainGap, emptyGap] using hThreshold a ha) with
    ⟨route, hroute, hinj⟩
  refine ⟨Atom, atoms, demand, route, hdemandNonneg, hRle, ?_, hinj, ?_⟩
  · intro a ha
    have hroute' := hroute a ha
    cases hslot : route a with
    | inl d =>
        have hmain : d ∈ I.image ∧ demand a ≤ mainGap d := by
          simpa [hslot] using hroute'
        exact hmain.1
    | inr u =>
        trivial
  · intro a ha
    have hroute' := hroute a ha
    cases hslot : route a with
    | inl d =>
        have hmain : d ∈ I.image ∧ demand a ≤ mainGap d := by
          simpa [hslot] using hroute'
        exact hmain.2
    | inr u =>
        simpa [hslot] using hroute'

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_iff_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical := by
  constructor
  · exact
      residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
  · exact
      residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge_iff_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical := by
  constructor
  · intro h
    exact
      residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
        (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge
          h)
  · exact
      residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_iff_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical := by
  constructor
  · exact
      residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
  · exact
      residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge_totalSlack
    {Atom MainSlot EmptySlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (emptySlots : Finset EmptySlot)
    {R boundaryMultiplicity restoredCopy mainBudget emptyBudget : ℝ}
    (demand : Atom → ℝ)
    (mainCap : MainSlot → ℝ)
    (emptyCap : EmptySlot → ℝ)
    (route : Atom → Sum MainSlot EmptySlot)
    (hmainCapNonneg : ∀ i ∈ mainSlots, 0 ≤ mainCap i)
    (hemptyCapNonneg : ∀ j ∈ emptySlots, 0 ≤ emptyCap j)
    (hR : R ≤ ∑ a ∈ atoms, demand a)
    (hrouteMap :
      ∀ a ∈ atoms,
        match route a with
        | Sum.inl i => i ∈ mainSlots
        | Sum.inr j => j ∈ emptySlots)
    (hrouteInjective : Set.InjOn route atoms)
    (hcover :
      ∀ a ∈ atoms,
        demand a ≤
          match route a with
          | Sum.inl i => mainCap i
          | Sum.inr j => emptyCap j)
    (hmain :
      (∑ i ∈ mainSlots, mainCap i) + boundaryMultiplicity ≤
        mainBudget)
    (hempty :
      (∑ j ∈ emptySlots, emptyCap j) + restoredCopy ≤
        emptyBudget) :
    R + (boundaryMultiplicity + restoredCopy) ≤ mainBudget + emptyBudget := by
  classical
  let reservoir : Finset (Sum MainSlot EmptySlot) :=
    mainSlots.image (Sum.inl : MainSlot → Sum MainSlot EmptySlot) ∪
      emptySlots.image (Sum.inr : EmptySlot → Sum MainSlot EmptySlot)
  let capacity : Sum MainSlot EmptySlot → ℝ := Sum.elim mainCap emptyCap
  have hmap : ∀ a ∈ atoms, route a ∈ reservoir := by
    intro a ha
    cases hroute : route a with
    | inl i =>
        have hi : i ∈ mainSlots := by
          simpa [hroute] using hrouteMap a ha
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    | inr j =>
        have hj : j ∈ emptySlots := by
          simpa [hroute] using hrouteMap a ha
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  have hcoverCapacity :
      ∀ a ∈ atoms, demand a ≤ capacity (route a) := by
    intro a ha
    cases hroute : route a with
    | inl i => simpa [capacity, hroute] using hcover a ha
    | inr j => simpa [capacity, hroute] using hcover a ha
  have hcapacityNonneg : ∀ r ∈ reservoir, 0 ≤ capacity r := by
    intro r hr
    cases r with
    | inl i =>
        have hi : i ∈ mainSlots := by
          rw [Finset.mem_union] at hr
          rcases hr with hmainMem | hemptyMem
          · rcases Finset.mem_image.mp hmainMem with ⟨i', hi', hiEq⟩
            simp only [Sum.inl.injEq] at hiEq
            simpa [hiEq] using hi'
          · rcases Finset.mem_image.mp hemptyMem with ⟨j, _hj, hbad⟩
            cases hbad
        simpa [capacity] using hmainCapNonneg i hi
    | inr j =>
        have hj : j ∈ emptySlots := by
          rw [Finset.mem_union] at hr
          rcases hr with hmainMem | hemptyMem
          · rcases Finset.mem_image.mp hmainMem with ⟨i, _hi, hbad⟩
            cases hbad
          · rcases Finset.mem_image.mp hemptyMem with ⟨j', hj', hjEq⟩
            simp only [Sum.inr.injEq] at hjEq
            simpa [hjEq] using hj'
        simpa [capacity] using hemptyCapNonneg j hj
  have hDemandLeCapacity :
      (∑ a ∈ atoms, demand a) ≤ ∑ r ∈ reservoir, capacity r :=
    finiteCharge_sum_le_sum_of_injective atoms reservoir route demand capacity
      hmap hrouteInjective hcoverCapacity hcapacityNonneg
  have hdisjoint :
      Disjoint
        (mainSlots.image (Sum.inl : MainSlot → Sum MainSlot EmptySlot))
        (emptySlots.image (Sum.inr : EmptySlot → Sum MainSlot EmptySlot)) := by
    rw [Finset.disjoint_left]
    intro r hmainMem hemptyMem
    rcases Finset.mem_image.mp hmainMem with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hemptyMem with ⟨j, _hj, hbad⟩
    cases hbad
  have hreservoirSplit :
      (∑ r ∈ reservoir, capacity r) =
        (∑ i ∈ mainSlots, mainCap i) +
          ∑ j ∈ emptySlots, emptyCap j := by
    dsimp [reservoir, capacity]
    rw [Finset.sum_union hdisjoint]
    rw [Finset.sum_image, Finset.sum_image]
    · simp
    · intro j _hj j' _hj' h
      exact Sum.inr.inj h
    · intro i _hi i' _hi' h
      exact Sum.inl.inj h
  calc
    R + (boundaryMultiplicity + restoredCopy) ≤
        ((∑ i ∈ mainSlots, mainCap i) +
            ∑ j ∈ emptySlots, emptyCap j) +
          (boundaryMultiplicity + restoredCopy) := by
      linarith
    _ =
        ((∑ i ∈ mainSlots, mainCap i) + boundaryMultiplicity) +
          ((∑ j ∈ emptySlots, emptyCap j) + restoredCopy) := by
      ring
    _ ≤ mainBudget + emptyBudget :=
      add_le_add hmain hempty

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget := (I.image.card : ℝ) * mainTerm
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    D + (boundaryMultiplicity + restoredCopy) ≤
      paid + (mainBudget + emptyBudget)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, MainSlot, EmptySlot, atoms, mainSlots, emptySlots, demand,
      mainCap, emptyCap, route, _hdemandNonneg, hmainCapNonneg,
      hemptyCapNonneg, hRle, hrouteMap, hrouteInjective, hcover,
      hmainCap, hemptyCap⟩
  have htotal :
      R + (boundaryMultiplicity + restoredCopy) ≤
        mainBudget + emptyBudget :=
    unpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge_totalSlack
      (atoms := atoms) (mainSlots := mainSlots) (emptySlots := emptySlots)
      (R := R) (boundaryMultiplicity := boundaryMultiplicity)
      (restoredCopy := restoredCopy) (mainBudget := mainBudget)
      (emptyBudget := emptyBudget) demand mainCap emptyCap route
      hmainCapNonneg hemptyCapNonneg hRle hrouteMap hrouteInjective hcover
      hmainCap hemptyCap
  linarith [show R = D - paid from rfl]

set_option linter.style.longLine false in


theorem unpaidRemainderReservoirSplitFallbackMixedFiniteInjectionCharge_totalSlack
    {k mainSlots emptySlots : ℕ}
    {R boundaryMultiplicity restoredCopy mainBudget emptyBudget : ℝ}
    {demand : Fin k → ℝ}
    {mainCap : Fin mainSlots → ℝ}
    {emptyCap : Fin emptySlots → ℝ}
    {route : Fin k → Sum (Fin mainSlots) (Fin emptySlots)}
    (_hdemandNonneg : ∀ a : Fin k, 0 ≤ demand a)
    (hmainCapNonneg : ∀ i : Fin mainSlots, 0 ≤ mainCap i)
    (hemptyCapNonneg : ∀ j : Fin emptySlots, 0 ≤ emptyCap j)
    (hR : R ≤ ∑ a : Fin k, demand a)
    (hrouteInjective : Function.Injective route)
    (hcover :
      ∀ a : Fin k,
        demand a ≤
          match route a with
          | Sum.inl i => mainCap i
          | Sum.inr j => emptyCap j)
    (hmain :
      (∑ i : Fin mainSlots, mainCap i) + boundaryMultiplicity ≤
        mainBudget)
    (hempty :
      (∑ j : Fin emptySlots, emptyCap j) + restoredCopy ≤
        emptyBudget) :
    R + (boundaryMultiplicity + restoredCopy) ≤ mainBudget + emptyBudget := by
  let capacity : Sum (Fin mainSlots) (Fin emptySlots) → ℝ :=
    Sum.elim mainCap emptyCap
  have hDemandLeCapacity :
      (∑ a : Fin k, demand a) ≤
        ∑ r : Sum (Fin mainSlots) (Fin emptySlots), capacity r := by
    simpa [capacity] using
      finiteCharge_sum_le_sum_of_injective
        (source := (Finset.univ : Finset (Fin k)))
        (reservoir :=
          (Finset.univ :
            Finset (Sum (Fin mainSlots) (Fin emptySlots))))
        (route := route) (demand := demand) (capacity := capacity)
        (by intro a _ha; exact Finset.mem_univ (route a))
        (by intro a _ha b _hb hroute; exact hrouteInjective hroute)
        (by
          intro a _ha
          cases hroute : route a with
          | inl i => simpa [capacity, hroute] using hcover a
          | inr j => simpa [capacity, hroute] using hcover a)
        (by
          intro r _hr
          cases r with
          | inl i => exact hmainCapNonneg i
          | inr j => exact hemptyCapNonneg j)
  have hcapacitySplit :
      (∑ r : Sum (Fin mainSlots) (Fin emptySlots), capacity r) =
        (∑ i : Fin mainSlots, mainCap i) +
          ∑ j : Fin emptySlots, emptyCap j := by
    simp [capacity, Fintype.sum_sum_type]
  calc
    R + (boundaryMultiplicity + restoredCopy) ≤
        ((∑ i : Fin mainSlots, mainCap i) +
            ∑ j : Fin emptySlots, emptyCap j) +
          (boundaryMultiplicity + restoredCopy) := by
      linarith
    _ =
        ((∑ i : Fin mainSlots, mainCap i) + boundaryMultiplicity) +
          ((∑ j : Fin emptySlots, emptyCap j) + restoredCopy) := by
      ring
    _ ≤ mainBudget + emptyBudget :=
      add_le_add hmain hempty

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget := (I.image.card : ℝ) * mainTerm
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    D + (boundaryMultiplicity + restoredCopy) ≤
      paid + (mainBudget + emptyBudget)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨k, mainSlots, emptySlots, demand, mainCap, emptyCap, route,
      hdemandNonneg, hmainCapNonneg, hemptyCapNonneg, hRle,
      hrouteInjective, hcover, hmainCap, hemptyCap⟩
  have htotal :
      R + (boundaryMultiplicity + restoredCopy) ≤
        mainBudget + emptyBudget :=
    unpaidRemainderReservoirSplitFallbackMixedFiniteInjectionCharge_totalSlack
      (k := k) (mainSlots := mainSlots) (emptySlots := emptySlots)
      (R := R) (boundaryMultiplicity := boundaryMultiplicity)
      (restoredCopy := restoredCopy) (mainBudget := mainBudget)
      (emptyBudget := emptyBudget) (demand := demand)
      (mainCap := mainCap) (emptyCap := emptyCap) (route := route)
      hdemandNonneg hmainCapNonneg hemptyCapNonneg hRle hrouteInjective
      hcover hmainCap hemptyCap
  linarith [show R = D - paid from rfl]

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget := (I.image.card : ℝ) * mainTerm
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    D + (boundaryMultiplicity + restoredCopy) ≤
      paid + (mainBudget + emptyBudget)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨k, demand, mainCharge, emptyCharge, _hdemandNonneg,
      _hmainChargeNonneg, _hemptyChargeNonneg, hRle, hcover, hmainCap,
      hemptyCap⟩
  have htotal :
      R + (boundaryMultiplicity + restoredCopy) ≤
        mainBudget + emptyBudget :=
    unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge_totalSlack
      (k := k) (R := R) (boundaryMultiplicity := boundaryMultiplicity)
      (restoredCopy := restoredCopy) (mainBudget := mainBudget)
      (emptyBudget := emptyBudget) (demand := demand)
      (mainCharge := mainCharge) (emptyCharge := emptyCharge)
      hRle hcover hmainCap hemptyCap
  linarith [show R = D - paid from rfl]

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_of_unpaidRemainderReservoirSplitBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    R ≤ mainGapSum + emptyGap
  intro hnonpos hmain hempty
  have hdisj :
      R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
        R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  exact
    (unpaidRemainderReservoirSplitBranchDisjunction_iff_le_mainEmptyGap_of_not_shortcuts
      hnonpos hmain hempty).mp hdisj

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_of_unpaidRemainderReservoirSplitFallbackMixed
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  by_cases hnonpos : R ≤ 0
  · exact Or.inl hnonpos
  · by_cases hmain : R ≤ mainGapSum
    · exact Or.inr (Or.inl hmain)
    · by_cases hempty : R ≤ emptyGap
      · exact Or.inr (Or.inr (Or.inl hempty))
      · have hmixed : R ≤ mainGapSum + emptyGap := by
          simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
            hn H hH Ω v hv hnonpos hmain hempty
        exact Or.inr (Or.inr (Or.inr hmixed))

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_of_unpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mixedDeficit := R - (mainGapSum + emptyGap)
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    R ≤ mainGapSum + emptyGap
  intro hnonpos hmain hempty
  have hdef : mixedDeficit ≤ 0 := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap, mixedDeficit]
      using hn H hH Ω v hv hnonpos hmain hempty
  exact
    (unpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_iff_le_mainEmptyGap).mp
      (by simpa [mixedDeficit] using hdef)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_of_unpaidRemainderReservoirSplitFallbackMixed
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mixedDeficit := R - (mainGapSum + emptyGap)
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    mixedDeficit ≤ 0
  intro hnonpos hmain hempty
  have hmixed : R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv hnonpos hmain hempty
  exact
    (unpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_iff_le_mainEmptyGap).mpr
      hmixed

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_iff_unpaidRemainderReservoirSplitFallbackMixed :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_of_unpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_of_unpaidRemainderReservoirSplitFallbackMixed⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_of_unpaidRemainderReservoirSplitFallbackMixedPaymentDominates
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    R ≤ mainGapSum + emptyGap
  intro hnonpos hmain hempty
  have hdom : D ≤ paid + mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv hnonpos hmain hempty
  have hmixed : D - paid ≤ mainGapSum + emptyGap :=
    (unpaidRemainderReservoirSplitFallbackMixedPaymentDominates_iff_le_mainEmptyGap).mp
      hdom
  simpa [R] using hmixed

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates_of_unpaidRemainderReservoirSplitFallbackMixed
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    D ≤ paid + mainGapSum + emptyGap
  intro hnonpos hmain hempty
  have hmixed : R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv hnonpos hmain hempty
  exact
    (unpaidRemainderReservoirSplitFallbackMixedPaymentDominates_iff_le_mainEmptyGap).mpr
      (by simpa [R] using hmixed)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates_iff_unpaidRemainderReservoirSplitFallbackMixed :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_of_unpaidRemainderReservoirSplitFallbackMixedPaymentDominates,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates_of_unpaidRemainderReservoirSplitFallbackMixed⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_of_unpaidRemainderReservoirSplitFallbackMixedExpandedDemand
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget := (I.image.card : ℝ) * mainTerm
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    R ≤ mainGapSum + emptyGap
  intro hnonpos hmain hempty
  have hexpanded :
      D + (boundaryMultiplicity + restoredCopy) ≤
        paid + (mainBudget + emptyBudget) := by
    simpa [Ωnz, cap, D, paid, R, I, mainTerm, boundaryMultiplicity,
      restoredCopy, mainBudget, emptyBudget, mainGapSum, emptyGap] using
      hn H hH Ω v hv hnonpos hmain hempty
  have hmainGap : mainGapSum = mainBudget - boundaryMultiplicity := by
    dsimp [mainGapSum, mainBudget, boundaryMultiplicity]
    calc
        (∑ d ∈ I.image,
            (mainTerm -
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                ℕ) : ℝ) *
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))) =
        (∑ _d ∈ I.image, mainTerm) -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_sub_distrib]
      _ =
        (I.image.card : ℝ) * mainTerm -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  exact
    (unpaidRemainderReservoirSplitFallbackMixedExpandedDemand_iff_le_mainEmptyGap
      (R := R) (D := D) (paid := paid) (mainGapSum := mainGapSum)
      (emptyGap := emptyGap) (boundaryMultiplicity := boundaryMultiplicity)
      (restoredCopy := restoredCopy) (mainBudget := mainBudget)
      (emptyBudget := emptyBudget) rfl hmainGap rfl).mp hexpanded

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixed
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget := (I.image.card : ℝ) * mainTerm
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    D + (boundaryMultiplicity + restoredCopy) ≤
      paid + (mainBudget + emptyBudget)
  intro hnonpos hmain hempty
  have hmixed : R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainTerm, mainGapSum, emptyGap] using
      hn H hH Ω v hv hnonpos hmain hempty
  have hmainGap : mainGapSum = mainBudget - boundaryMultiplicity := by
    dsimp [mainGapSum, mainBudget, boundaryMultiplicity]
    calc
        (∑ d ∈ I.image,
            (mainTerm -
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                ℕ) : ℝ) *
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))) =
        (∑ _d ∈ I.image, mainTerm) -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_sub_distrib]
      _ =
        (I.image.card : ℝ) * mainTerm -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  exact
    (unpaidRemainderReservoirSplitFallbackMixedExpandedDemand_iff_le_mainEmptyGap
      (R := R) (D := D) (paid := paid) (mainGapSum := mainGapSum)
      (emptyGap := emptyGap) (boundaryMultiplicity := boundaryMultiplicity)
      (restoredCopy := restoredCopy) (mainBudget := mainBudget)
      (emptyBudget := emptyBudget) rfl hmainGap rfl).mpr hmixed

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_iff_unpaidRemainderReservoirSplitFallbackMixed :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_of_unpaidRemainderReservoirSplitFallbackMixedExpandedDemand,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixed⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_iff_unpaidRemainderReservoirSplitBranchDisjunction :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_of_unpaidRemainderReservoirSplitFallbackMixed,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_of_unpaidRemainderReservoirSplitBranchDisjunction⟩

end Exact3D
end StatMech
