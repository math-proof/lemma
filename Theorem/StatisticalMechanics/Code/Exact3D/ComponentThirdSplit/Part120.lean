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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part129
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_mem_compatible
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    {a : Atom} {slot : Sum MainSlot Unit}
    (hslot :
      slot ∈
        canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a) :
    match slot with
    | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
    | Sum.inr _ => demand a ≤ emptyCap := by
  classical
  unfold canonicalCapacityCandidateSlots at hslot
  rw [Finset.mem_union] at hslot
  cases slot with
  | inl d =>
      rcases hslot with hmain | hempty
      · rcases Finset.mem_image.mp hmain with ⟨d', hd', hdEq⟩
        simp only [Sum.inl.injEq] at hdEq
        rw [Finset.mem_filter] at hd'
        exact ⟨by simpa [hdEq] using hd'.1, by simpa [hdEq] using hd'.2⟩
      · rcases Finset.mem_image.mp hempty with ⟨u, _hu, hbad⟩
        cases hbad
  | inr u =>
      rcases hslot with hmain | hempty
      · rcases Finset.mem_image.mp hmain with ⟨d, _hd, hbad⟩
        cases hbad
      · rcases Finset.mem_image.mp hempty with ⟨u', hu', _huEq⟩
        rw [Finset.mem_filter] at hu'
        exact hu'.2

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_mem_of_compatible
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    {a : Atom} {slot : Sum MainSlot Unit}
    (hcompat :
      match slot with
      | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
      | Sum.inr _ => demand a ≤ emptyCap) :
    slot ∈
      canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
  classical
  unfold canonicalCapacityCandidateSlots
  cases slot with
  | inl d =>
      rw [Finset.mem_union]
      left
      exact
        Finset.mem_image.mpr
          ⟨d, Finset.mem_filter.mpr hcompat, rfl⟩
  | inr u =>
      rw [Finset.mem_union]
      right
      exact
        Finset.mem_image.mpr
          ⟨u, Finset.mem_filter.mpr ⟨by simp, hcompat⟩, rfl⟩

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_nonempty_iff
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom) :
    (canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a).Nonempty ↔
      (∃ d, d ∈ mainSlots ∧ demand a ≤ mainCap d) ∨
        demand a ≤ emptyCap := by
  constructor
  · rintro ⟨slot, hslot⟩
    have hcompat :=
      canonicalCapacityCandidateSlots_mem_compatible
        mainSlots mainCap emptyCap demand hslot
    cases slot with
    | inl d =>
        exact Or.inl ⟨d, hcompat⟩
    | inr u =>
        exact Or.inr hcompat
  · rintro (⟨d, hd, hcap⟩ | hempty)
    · exact
        ⟨Sum.inl d,
          canonicalCapacityCandidateSlots_mem_of_compatible
            (mainSlots := mainSlots) (mainCap := mainCap)
            (emptyCap := emptyCap) (demand := demand) (a := a)
            (slot := Sum.inl d) ⟨hd, hcap⟩⟩
    · exact
        ⟨Sum.inr (),
          canonicalCapacityCandidateSlots_mem_of_compatible
            (mainSlots := mainSlots) (mainCap := mainCap)
            (emptyCap := emptyCap) (demand := demand) (a := a)
            (slot := Sum.inr ()) hempty⟩

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_eq_empty_iff
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom) :
    canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a = ∅ ↔
      (∀ d, d ∈ mainSlots → ¬ demand a ≤ mainCap d) ∧
        ¬ demand a ≤ emptyCap := by
  rw [← Finset.not_nonempty_iff_eq_empty,
    canonicalCapacityCandidateSlots_nonempty_iff]
  constructor
  · intro hnonempty
    constructor
    · intro d hd hcap
      exact hnonempty (Or.inl ⟨d, hd, hcap⟩)
    · intro hempty
      exact hnonempty (Or.inr hempty)
  · rintro ⟨hmain, hempty⟩ (⟨d, hd, hcap⟩ | hcap)
    · exact hmain d hd hcap
    · exact hempty hcap

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_subset_of_demand_le
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    {a b : Atom}
    (hab : demand a ≤ demand b) :
    canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand b ⊆
      canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
  intro slot hslot
  have hcompat :=
    canonicalCapacityCandidateSlots_mem_compatible
      mainSlots mainCap emptyCap demand hslot
  cases slot with
  | inl d =>
      exact
        canonicalCapacityCandidateSlots_mem_of_compatible
          (mainSlots := mainSlots) (mainCap := mainCap)
          (emptyCap := emptyCap) (demand := demand) (a := a)
          (slot := Sum.inl d)
          ⟨hcompat.1, le_trans hab hcompat.2⟩
  | inr u =>
      exact
        canonicalCapacityCandidateSlots_mem_of_compatible
          (mainSlots := mainSlots) (mainCap := mainCap)
          (emptyCap := emptyCap) (demand := demand) (a := a)
          (slot := Sum.inr u)
          (le_trans hab hcompat)

set_option linter.style.longLine false in

theorem canonicalCapacityCandidateSlots_card_le_of_demand_le
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    {a b : Atom}
    (hab : demand a ≤ demand b) :
    (canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand b).card ≤
      (canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a).card :=
  Finset.card_le_card
    (canonicalCapacityCandidateSlots_subset_of_demand_le
      (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) hab)

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_biUnion_thresholdTail_eq
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    {a : Atom}
    (ha : a ∈ atoms) :
    (@Finset.biUnion Atom (Sum MainSlot Unit)
        (Classical.decEq (Sum MainSlot Unit))
        (atoms.filter (fun b => demand a ≤ demand b))
        (canonicalCapacityCandidateSlots
          mainSlots mainCap emptyCap demand)) =
      canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a := by
  classical
  ext slot
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨b, hb, hslotb⟩
    have hb' := Finset.mem_filter.mp hb
    exact
      canonicalCapacityCandidateSlots_subset_of_demand_le
        (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) hb'.2 hslotb
  · intro hslot
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, le_rfl⟩, hslot⟩

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_disjoint_iff
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a b : Atom) :
    Disjoint
        (canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a)
        (canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand b) ↔
      (∀ d, d ∈ mainSlots →
        ¬ (demand a ≤ mainCap d ∧ demand b ≤ mainCap d)) ∧
        ¬ (demand a ≤ emptyCap ∧ demand b ≤ emptyCap) := by
  classical
  constructor
  · intro hdisj
    constructor
    · intro d hd hboth
      have hslotA :
          Sum.inl d ∈
            canonicalCapacityCandidateSlots
              mainSlots mainCap emptyCap demand a := by
        unfold canonicalCapacityCandidateSlots
        rw [Finset.mem_union]
        left
        exact
          Finset.mem_image.mpr
            ⟨d, Finset.mem_filter.mpr ⟨hd, hboth.1⟩, rfl⟩
      have hslotB :
          Sum.inl d ∈
            canonicalCapacityCandidateSlots
              mainSlots mainCap emptyCap demand b := by
        unfold canonicalCapacityCandidateSlots
        rw [Finset.mem_union]
        left
        exact
          Finset.mem_image.mpr
            ⟨d, Finset.mem_filter.mpr ⟨hd, hboth.2⟩, rfl⟩
      exact (Finset.disjoint_left.mp hdisj hslotA) hslotB
    · intro hboth
      have hslotA :
          Sum.inr () ∈
            canonicalCapacityCandidateSlots
              mainSlots mainCap emptyCap demand a := by
        unfold canonicalCapacityCandidateSlots
        rw [Finset.mem_union]
        right
        exact
          Finset.mem_image.mpr
            ⟨(), Finset.mem_filter.mpr ⟨by simp, hboth.1⟩, rfl⟩
      have hslotB :
          Sum.inr () ∈
            canonicalCapacityCandidateSlots
              mainSlots mainCap emptyCap demand b := by
        unfold canonicalCapacityCandidateSlots
        rw [Finset.mem_union]
        right
        exact
          Finset.mem_image.mpr
            ⟨(), Finset.mem_filter.mpr ⟨by simp, hboth.2⟩, rfl⟩
      exact (Finset.disjoint_left.mp hdisj hslotA) hslotB
  · rintro ⟨hmain, hempty⟩
    rw [Finset.disjoint_left]
    intro slot hslotA hslotB
    have hcompatA :=
      canonicalCapacityCandidateSlots_mem_compatible
        mainSlots mainCap emptyCap demand hslotA
    have hcompatB :=
      canonicalCapacityCandidateSlots_mem_compatible
        mainSlots mainCap emptyCap demand hslotB
    cases slot with
    | inl d =>
        exact hmain d hcompatA.1 ⟨hcompatA.2, hcompatB.2⟩
    | inr u =>
        exact hempty ⟨hcompatA, hcompatB⟩

theorem not_both_le_iff_lt_max {x y c : ℝ} :
    ¬ (x ≤ c ∧ y ≤ c) ↔ c < max x y := by
  constructor
  · intro h
    by_contra hnot
    have hmax : max x y ≤ c := le_of_not_gt hnot
    exact h
      ⟨le_trans (le_max_left x y) hmax,
        le_trans (le_max_right x y) hmax⟩
  · intro hc hboth
    exact not_le_of_gt hc (max_le hboth.1 hboth.2)

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_disjoint_iff_capacity_lt_max
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a b : Atom) :
    Disjoint
        (canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a)
        (canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand b) ↔
      (∀ d, d ∈ mainSlots →
        mainCap d < max (demand a) (demand b)) ∧
        emptyCap < max (demand a) (demand b) := by
  rw [canonicalCapacityCandidateSlots_disjoint_iff]
  constructor
  · rintro ⟨hmain, hempty⟩
    constructor
    · intro d hd
      exact
        (not_both_le_iff_lt_max
          (x := demand a) (y := demand b) (c := mainCap d)).mp
          (hmain d hd)
    · exact
        (not_both_le_iff_lt_max
          (x := demand a) (y := demand b) (c := emptyCap)).mp
          hempty
  · rintro ⟨hmain, hempty⟩
    constructor
    · intro d hd
      exact
        (not_both_le_iff_lt_max
          (x := demand a) (y := demand b) (c := mainCap d)).mpr
          (hmain d hd)
    · exact
        (not_both_le_iff_lt_max
          (x := demand a) (y := demand b) (c := emptyCap)).mpr
          hempty

set_option linter.style.longLine false in


theorem canonicalCapacityCandidateSlots_card
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom) :
    (canonicalCapacityCandidateSlots mainSlots mainCap emptyCap demand a).card =
      (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
        if demand a ≤ emptyCap then 1 else 0 := by
  classical
  unfold canonicalCapacityCandidateSlots
  let mainCandidates :=
    mainSlots.filter (fun d => demand a ≤ mainCap d)
  let emptyCandidates :=
    (Finset.univ : Finset Unit).filter (fun _ => demand a ≤ emptyCap)
  have hdisj :
      Disjoint
        (mainCandidates.image (Sum.inl : MainSlot → Sum MainSlot Unit))
        (emptyCandidates.image (Sum.inr : Unit → Sum MainSlot Unit)) := by
    rw [Finset.disjoint_left]
    intro slot hmain hempty
    rcases Finset.mem_image.mp hmain with ⟨d, _hd, hslotMain⟩
    rcases Finset.mem_image.mp hempty with ⟨u, _hu, hslotEmpty⟩
    have hbad : Sum.inl d = Sum.inr u := hslotMain.trans hslotEmpty.symm
    cases hbad
  rw [Finset.card_union_of_disjoint hdisj]
  have hmainCard :
      (mainCandidates.image (Sum.inl : MainSlot → Sum MainSlot Unit)).card =
        mainCandidates.card := by
    exact
      Finset.card_image_of_injective mainCandidates
        (fun d e hde => Sum.inl.inj hde)
  have hemptyCard :
      (emptyCandidates.image (Sum.inr : Unit → Sum MainSlot Unit)).card =
        emptyCandidates.card := by
    exact
      Finset.card_image_of_injective emptyCandidates
        (fun u w huw => Sum.inr.inj huw)
  rw [hmainCard, hemptyCard]
  by_cases hempty : demand a ≤ emptyCap
  · have hfilter :
        emptyCandidates = (Finset.univ : Finset Unit) := by
      ext u
      simp [emptyCandidates, hempty]
    simp [mainCandidates, emptyCandidates, hfilter, hempty]
  · have hfilter :
        emptyCandidates = (∅ : Finset Unit) := by
      ext u
      simp [emptyCandidates, hempty]
    simp [mainCandidates, emptyCandidates, hfilter, hempty]

set_option linter.style.longLine false in


theorem canonicalCapacityThresholdScalarCount_of_thresholdRouteInjOn
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom)
    (route : Atom → Sum MainSlot Unit)
    (hroute :
      ∀ b, b ∈ atoms → demand a ≤ demand b →
        match route b with
        | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
        | Sum.inr _ => demand a ≤ emptyCap)
    (hinj :
      Set.InjOn route
        (atoms.filter (fun b => demand a ≤ demand b) : Set Atom)) :
    (atoms.filter (fun b => demand a ≤ demand b)).card ≤
      (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
        if demand a ≤ emptyCap then 1 else 0 := by
  classical
  have hmaps :
      Set.MapsTo route
        (atoms.filter (fun b => demand a ≤ demand b) : Set Atom)
        (canonicalCapacityCandidateSlots
          mainSlots mainCap emptyCap demand a : Set (Sum MainSlot Unit)) := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    exact
      canonicalCapacityCandidateSlots_mem_of_compatible
        (mainSlots := mainSlots) (mainCap := mainCap)
        (emptyCap := emptyCap) (demand := demand) (a := a)
        (slot := route b) (hroute b hb'.1 hb'.2)
  have hle :
      (atoms.filter (fun b => demand a ≤ demand b)).card ≤
        (canonicalCapacityCandidateSlots
          mainSlots mainCap emptyCap demand a).card :=
    Finset.card_le_card_of_injOn route hmaps hinj
  calc
    (atoms.filter (fun b => demand a ≤ demand b)).card ≤
        (canonicalCapacityCandidateSlots
          mainSlots mainCap emptyCap demand a).card := hle
    _ =
        (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
          if demand a ≤ emptyCap then 1 else 0 :=
        canonicalCapacityCandidateSlots_card
          (mainSlots := mainSlots) (mainCap := mainCap)
          (emptyCap := emptyCap) (demand := demand) (a := a)

set_option linter.style.longLine false in


theorem canonicalCapacityThresholdScalarCount_of_globalRouteInjOn
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (route : Atom → Sum MainSlot Unit)
    (hroute :
      ∀ b, b ∈ atoms →
        match route b with
        | Sum.inl d => d ∈ mainSlots ∧ demand b ≤ mainCap d
        | Sum.inr _ => demand b ≤ emptyCap)
    (hinj : Set.InjOn route (atoms : Set Atom)) :
    ∀ a, a ∈ atoms →
      (atoms.filter (fun b => demand a ≤ demand b)).card ≤
        (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
          if demand a ≤ emptyCap then 1 else 0 := by
  intro a _ha
  refine
    canonicalCapacityThresholdScalarCount_of_thresholdRouteInjOn
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) (a := a)
      (route := route) ?_ ?_
  · intro b hb hle
    have hbroute := hroute b hb
    cases hslot : route b with
    | inl d =>
        rw [hslot] at hbroute
        exact ⟨hbroute.1, le_trans hle hbroute.2⟩
    | inr u =>
        rw [hslot] at hbroute
        exact le_trans hle hbroute
  · intro b hb c hc hbc
    exact
      hinj
        (Finset.mem_filter.mp hb).1
        (Finset.mem_filter.mp hc).1
        hbc

set_option linter.style.longLine false in


theorem canonicalCapacityThresholdScalarCount_of_thresholdSubtypeRoute
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom)
    (route : {b // b ∈ atoms ∧ demand a ≤ demand b} → Sum MainSlot Unit)
    (hroute :
      ∀ b,
        match route b with
        | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
        | Sum.inr _ => demand a ≤ emptyCap)
    (hinj : Function.Injective route) :
    (atoms.filter (fun b => demand a ≤ demand b)).card ≤
      (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
        if demand a ≤ emptyCap then 1 else 0 := by
  classical
  let route' : Atom → Sum MainSlot Unit :=
    fun b =>
      if hb : b ∈ atoms ∧ demand a ≤ demand b then
        route ⟨b, hb⟩
      else
        Sum.inr ()
  have hroute' :
      ∀ b, b ∈ atoms → demand a ≤ demand b →
        match route' b with
        | Sum.inl d => d ∈ mainSlots ∧ demand a ≤ mainCap d
        | Sum.inr _ => demand a ≤ emptyCap := by
    intro b hb hle
    have hbsub : b ∈ atoms ∧ demand a ≤ demand b := ⟨hb, hle⟩
    simpa [route', hbsub] using hroute ⟨b, hbsub⟩
  have hinj' :
      Set.InjOn route'
        (atoms.filter (fun b => demand a ≤ demand b) : Set Atom) := by
    intro b hb c hc hbc
    have hb' := Finset.mem_filter.mp hb
    have hc' := Finset.mem_filter.mp hc
    have hbsub : b ∈ atoms ∧ demand a ≤ demand b := hb'
    have hcsub : c ∈ atoms ∧ demand a ≤ demand c := hc'
    have hrouteEq : route ⟨b, hbsub⟩ = route ⟨c, hcsub⟩ := by
      simpa [route', hbsub, hcsub] using hbc
    exact congrArg Subtype.val (hinj hrouteEq)
  exact
    canonicalCapacityThresholdScalarCount_of_thresholdRouteInjOn
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) (a := a)
      (route := route') hroute' hinj'

set_option linter.style.longLine false in


theorem canonicalCapacityThresholdScalarCount_of_thresholdCandidateEmbedding
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom)
    (route :
      {b // b ∈ atoms ∧ demand a ≤ demand b} ↪
        {slot : Sum MainSlot Unit //
          slot ∈ canonicalCapacityCandidateSlots
            mainSlots mainCap emptyCap demand a}) :
    (atoms.filter (fun b => demand a ≤ demand b)).card ≤
      (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
        if demand a ≤ emptyCap then 1 else 0 :=
  canonicalCapacityThresholdScalarCount_of_thresholdSubtypeRoute
    (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
    (emptyCap := emptyCap) (demand := demand) (a := a)
    (route := fun b => (route b).1)
    (hroute := by
      intro b
      cases hslot : (route b).1 with
      | inl d =>
          have hmem :
              Sum.inl d ∈
                canonicalCapacityCandidateSlots
                  mainSlots mainCap emptyCap demand a := by
            simpa [hslot] using (route b).2
          simpa [hslot] using
            (canonicalCapacityCandidateSlots_mem_compatible
              (mainSlots := mainSlots) (mainCap := mainCap)
              (emptyCap := emptyCap) (demand := demand) (a := a)
              (slot := Sum.inl d) hmem)
      | inr u =>
          have hmem :
              Sum.inr u ∈
                canonicalCapacityCandidateSlots
                  mainSlots mainCap emptyCap demand a := by
            simpa [hslot] using (route b).2
          simpa [hslot] using
            (canonicalCapacityCandidateSlots_mem_compatible
              (mainSlots := mainSlots) (mainCap := mainCap)
              (emptyCap := emptyCap) (demand := demand) (a := a)
              (slot := Sum.inr u) hmem))
    (hinj := by
      intro b c hbc
      apply route.injective
      exact Subtype.ext hbc)

set_option linter.style.longLine false in


theorem canonicalCapacityThresholdCandidateEmbedding_of_thresholdCandidateCard
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom)
    (hcard :
      (atoms.filter (fun b => demand a ≤ demand b)).card ≤
        (canonicalCapacityCandidateSlots
          mainSlots mainCap emptyCap demand a).card) :
    Nonempty
      ({b // b ∈ atoms ∧ demand a ≤ demand b} ↪
        {slot : Sum MainSlot Unit //
          slot ∈
            canonicalCapacityCandidateSlots
              mainSlots mainCap emptyCap demand a}) := by
  classical
  let e : {b // b ∈ atoms ∧ demand a ≤ demand b} ≃
      {b // b ∈ atoms.filter (fun b => demand a ≤ demand b)} := {
    toFun := fun b => ⟨b.1, Finset.mem_filter.mpr b.2⟩
    invFun := fun b => ⟨b.1, Finset.mem_filter.mp b.2⟩
    left_inv := by
      intro b
      ext
      rfl
    right_inv := by
      intro b
      ext
      rfl }
  letI : Fintype {b // b ∈ atoms ∧ demand a ≤ demand b} :=
    Fintype.ofEquiv
      {b // b ∈ atoms.filter (fun b => demand a ≤ demand b)}
      e.symm
  have hsrc :
      Fintype.card {b // b ∈ atoms ∧ demand a ≤ demand b} =
        (atoms.filter (fun b => demand a ≤ demand b)).card := by
    have h1 :
        Fintype.card {b // b ∈ atoms ∧ demand a ≤ demand b} =
          Fintype.card
            {b // b ∈ atoms.filter (fun b => demand a ≤ demand b)} :=
      Fintype.card_congr e
    have h2 :
        Fintype.card
            {b // b ∈ atoms.filter (fun b => demand a ≤ demand b)} =
          (atoms.filter (fun b => demand a ≤ demand b)).card :=
      Fintype.card_coe _
    exact h1.trans h2
  have htgt :
      Fintype.card
          {slot : Sum MainSlot Unit //
            slot ∈
              canonicalCapacityCandidateSlots
                mainSlots mainCap emptyCap demand a} =
        (canonicalCapacityCandidateSlots
          mainSlots mainCap emptyCap demand a).card :=
    Fintype.card_coe _
  exact
    Function.Embedding.nonempty_of_card_le (by
      simpa [hsrc, htgt] using hcard)

set_option linter.style.longLine false in


theorem canonicalCapacityThresholdCandidateEmbedding_of_thresholdScalarCount
    {Atom MainSlot : Type*}
    (atoms : Finset Atom)
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom)
    (hcard :
      (atoms.filter (fun b => demand a ≤ demand b)).card ≤
        (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
          if demand a ≤ emptyCap then 1 else 0) :
    Nonempty
      ({b // b ∈ atoms ∧ demand a ≤ demand b} ↪
        {slot : Sum MainSlot Unit //
          slot ∈
            canonicalCapacityCandidateSlots
              mainSlots mainCap emptyCap demand a}) := by
  apply
    canonicalCapacityThresholdCandidateEmbedding_of_thresholdCandidateCard
      (atoms := atoms) (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) (a := a)
  have hslots :
      (canonicalCapacityCandidateSlots
          mainSlots mainCap emptyCap demand a).card =
        (mainSlots.filter (fun d => demand a ≤ mainCap d)).card +
          if demand a ≤ emptyCap then 1 else 0 :=
    canonicalCapacityCandidateSlots_card
      (mainSlots := mainSlots) (mainCap := mainCap)
      (emptyCap := emptyCap) (demand := demand) (a := a)
  simpa [hslots] using hcard

end Exact3D
end StatMech
