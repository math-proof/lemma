/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc_doubledboxcount
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


@[simp] lemma mem_disjointPairs {𝒜 ℬ : Finset (Finset α)} {p : Finset α × Finset α} :
    p ∈ disjointPairs 𝒜 ℬ ↔ (p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ) ∧ Disjoint p.1 p.2 := by
  simp only [disjointPairs, mem_filter, mem_product]


theorem rc_dpairsCount_eq (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = (disjointPairs 𝒜 ℬ).card := rfl


theorem rc_dbl_injOn_disjoint (𝒜 ℬ : Finset (Finset α)) :
    Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) (disjointPairs 𝒜 ℬ) :=
  dbl_injective.injOn


theorem rc_boxDoubled_eq_image (𝒜 ℬ : Finset (Finset α)) :
    boxDoubled 𝒜 ℬ = (disjointPairs 𝒜 ℬ).image (fun p => dbl p.1 p.2) := rfl


theorem rc_card_boxDoubled_eq_dpairsViaInjOn (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
  rw [rc_boxDoubled_eq_image, Finset.card_image_of_injOn (rc_dbl_injOn_disjoint 𝒜 ℬ),
    rc_dpairsCount_eq]


theorem rc_doubledBoxCount (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ ∧
    dpairsCount 𝒜 ℬ = (disjointPairs 𝒜 ℬ).card :=
  ⟨rc_card_boxDoubled_eq_dpairsViaInjOn 𝒜 ℬ, rc_dpairsCount_eq 𝒜 ℬ⟩


theorem rc_union_not_injOn_disjoint (a : α) :
    ¬ Set.InjOn (fun p : Finset α × Finset α => p.1 ∪ p.2)
        (disjointPairs ({∅, {a}} : Finset (Finset α)) {∅, {a}}) := by
  intro hinj
  have hp1 : (({a}, ∅) : Finset α × Finset α) ∈
      disjointPairs ({∅, {a}} : Finset (Finset α)) {∅, {a}} := by
    rw [mem_disjointPairs]
    exact ⟨⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      Finset.mem_insert_self _ _⟩, by simp⟩
  have hp2 : ((∅, {a}) : Finset α × Finset α) ∈
      disjointPairs ({∅, {a}} : Finset (Finset α)) {∅, {a}} := by
    rw [mem_disjointPairs]
    exact ⟨⟨Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, by simp⟩
  have hunion : (({a}, ∅) : Finset α × Finset α).1 ∪ (({a}, ∅) : Finset α × Finset α).2
      = ((∅, {a}) : Finset α × Finset α).1 ∪ ((∅, {a}) : Finset α × Finset α).2 := by simp
  have := hinj hp1 hp2 hunion
  
  have hne : (({a}, ∅) : Finset α × Finset α) ≠ ((∅, {a}) : Finset α × Finset α) := by
    intro h
    have : ({a} : Finset α) = (∅ : Finset α) := congrArg Prod.fst h
    exact (Finset.singleton_ne_empty a) this
  exact hne this


theorem rc_card_boxFamily_le_dpairsCount (𝒜 ℬ : Finset (Finset α)) :
    (boxFamily 𝒜 ℬ).card ≤ dpairsCount 𝒜 ℬ := by
  rw [← rc_card_boxDoubled_eq_dpairsViaInjOn]
  exact card_boxFamily_le_boxDoubled 𝒜 ℬ


end StatMech.Walls
