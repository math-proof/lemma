/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part6


namespace StatMech.FrontierA

@[simp] theorem RelationPartialMatching.reassign_apply_new
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) :
    (matching.reassign new old b hne hold hnew).toFun new = some b := by
  classical
  simp [RelationPartialMatching.reassign]

@[simp] theorem RelationPartialMatching.reassign_apply_old
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) :
    (matching.reassign new old b hne hold hnew).toFun old = none := by
  classical
  simp [RelationPartialMatching.reassign, hne.symm]

theorem RelationPartialMatching.reassign_apply_of_ne
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old x : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) (hxNew : x ≠ new) (hxOld : x ≠ old) :
    (matching.reassign new old b hne hold hnew).toFun x = matching.toFun x := by
  classical
  simp [RelationPartialMatching.reassign, hxNew, hxOld]


theorem RelationPartialMatching.support_reassign
    {A B : Type*} [Fintype A] [DecidableEq A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) :
    (matching.reassign new old b hne hold hnew).support =
      insert new (matching.support.erase old) := by
  classical
  ext x
  by_cases hxNew : x = new
  · subst x
    simp [RelationPartialMatching.mem_support_iff]
  · by_cases hxOld : x = old
    · subst x
      simp [RelationPartialMatching.mem_support_iff, hne.symm]
    · simp [RelationPartialMatching.mem_support_iff,
        RelationPartialMatching.reassign_apply_of_ne,
        hxNew, hxOld]


theorem RelationPartialMatching.ne_of_not_mem_support_of_eq_some
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hnewUnmatched : new ∉ matching.support)
    (hold : matching.toFun old = some b) : new ≠ old := by
  intro h
  subst old
  exact hnewUnmatched
    ((RelationPartialMatching.mem_support_iff matching new).2 ⟨b, hold⟩)


theorem RelationPartialMatching.card_support_reassign
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hnewUnmatched : new ∉ matching.support)
    (hold : matching.toFun old = some b) (hnew : r new b) :
    (matching.reassign new old b
      (matching.ne_of_not_mem_support_of_eq_some
        new old b hnewUnmatched hold)
      hold hnew).support.card = matching.support.card := by
  classical
  let hne : new ≠ old := matching.ne_of_not_mem_support_of_eq_some
    new old b hnewUnmatched hold
  have holdMem : old ∈ matching.support :=
    (RelationPartialMatching.mem_support_iff matching old).2 ⟨b, hold⟩
  have hcardPositive : 0 < matching.support.card :=
    Finset.card_pos.mpr ⟨old, holdMem⟩
  have hnewErase : new ∉ matching.support.erase old := by
    simp only [Finset.mem_erase, not_and_or]
    exact Or.inr hnewUnmatched
  rw [RelationPartialMatching.support_reassign]
  rw [Finset.card_insert_of_notMem hnewErase,
    Finset.card_erase_of_mem holdMem]
  omega


theorem RelationPartialMatching.IsMaximum.reassign
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    {matching : RelationPartialMatching r} (hmaximum : matching.IsMaximum)
    (new old : A) (b : B) (hnewUnmatched : new ∉ matching.support)
    (hold : matching.toFun old = some b) (hnew : r new b) :
    (matching.reassign new old b
      (matching.ne_of_not_mem_support_of_eq_some
        new old b hnewUnmatched hold)
      hold hnew).IsMaximum := by
  intro other
  rw [RelationPartialMatching.card_support_reassign
    matching new old b hnewUnmatched hold hnew]
  exact hmaximum other


theorem RelationPartialMatching.IsMaximum.saturates_target_of_unmatched
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    {matching : RelationPartialMatching r} (hmaximum : matching.IsMaximum)
    (a : A) (ha : a ∉ matching.support) (b : B) (hab : r a b) :
    ∃ a', matching.toFun a' = some b := by
  classical
  by_contra hunused
  push Not at hunused
  let extendedFun : A -> Option B := fun x =>
    if x = a then some b else matching.toFun x
  have hextendedRelated : ∀ {x y}, extendedFun x = some y -> r x y := by
    intro x y hxy
    by_cases hx : x = a
    · subst x
      simp only [extendedFun, if_pos] at hxy
      exact Option.some.inj hxy ▸ hab
    · simp only [extendedFun, if_neg hx] at hxy
      exact matching.related hxy
  have hextendedInjective : ∀ {x y z},
      extendedFun x = some z -> extendedFun y = some z -> x = y := by
    intro x y z hx hy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      · simp only [extendedFun, if_pos, Option.some.injEq] at hx
        simp only [extendedFun, if_neg hya] at hy
        exact False.elim (hunused y (hy.trans (congrArg some hx.symm)))
    · by_cases hya : y = a
      · subst y
        simp only [extendedFun, if_neg hxa] at hx
        simp only [extendedFun, if_pos, Option.some.injEq] at hy
        exact False.elim (hunused x (hx.trans (congrArg some hy.symm)))
      · simp only [extendedFun, if_neg hxa] at hx
        simp only [extendedFun, if_neg hya] at hy
        exact matching.injective_some hx hy
  let extended : RelationPartialMatching r :=
    ⟨extendedFun, hextendedRelated, hextendedInjective⟩
  have hsupport : extended.support = insert a matching.support := by
    ext x
    by_cases hx : x = a
    · subst x
      simp [RelationPartialMatching.mem_support_iff, extended, extendedFun]
    · simp [RelationPartialMatching.mem_support_iff, extended, extendedFun, hx]
  have hcard : extended.support.card = matching.support.card + 1 := by
    rw [hsupport, Finset.card_insert_of_notMem ha]
  have hle := hmaximum extended
  omega


theorem RelationPartialMatching.card_support_le_target
    {A B : Type*} [Fintype A] [Fintype B] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) :
    matching.support.card ≤ Fintype.card B := by
  classical
  let target : {a : A // a ∈ matching.support} -> B := fun a =>
    Classical.choose
      ((RelationPartialMatching.mem_support_iff matching a.1).1 a.2)
  have htarget (a : {a : A // a ∈ matching.support}) :
      matching.toFun a.1 = some (target a) :=
    Classical.choose_spec
      ((RelationPartialMatching.mem_support_iff matching a.1).1 a.2)
  have hinjective : Function.Injective target := by
    intro a b hab
    apply Subtype.ext
    exact matching.injective_some (htarget a)
      ((htarget b).trans (congrArg some hab.symm))
  have hcard := Fintype.card_le_of_injective target hinjective
  simpa only [Fintype.card_coe] using hcard


theorem RelationPartialMatching.saturates_all_targets_of_card_support_eq
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    {r : A -> B -> Prop} (matching : RelationPartialMatching r)
    (hcard : matching.support.card = Fintype.card B) (b : B) :
    ∃ a, matching.toFun a = some b := by
  classical
  let Supported := {a : A // a ∈ matching.support}
  let target : Supported -> B := fun a =>
    Classical.choose
      ((RelationPartialMatching.mem_support_iff matching a.1).1 a.2)
  have htarget (a : Supported) :
      matching.toFun a.1 = some (target a) :=
    Classical.choose_spec
      ((RelationPartialMatching.mem_support_iff matching a.1).1 a.2)
  have hinjective : Function.Injective target := by
    intro a c hac
    apply Subtype.ext
    exact matching.injective_some (htarget a)
      ((htarget c).trans (congrArg some hac.symm))
  have hcardTypes : Fintype.card Supported = Fintype.card B := by
    simpa only [Supported, Fintype.card_coe] using hcard
  have hsurjective : Function.Surjective target :=
    ((Fintype.bijective_iff_injective_and_card target).2
      ⟨hinjective, hcardTypes⟩).2
  obtain ⟨a, ha⟩ := hsurjective b
  exact ⟨a.1, (htarget a).trans (congrArg some ha)⟩


end StatMech.FrontierA
