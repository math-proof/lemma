/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc5_doubledboxcount
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


@[simp] lemma rc5_mem_dpairs {𝒜 ℬ : Finset (Finset α)} {p : Finset α × Finset α} :
    p ∈ rc5_dpairs 𝒜 ℬ ↔ (p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ) ∧ Disjoint p.1 p.2 := by
  simp only [rc5_dpairs, mem_filter, mem_product]


theorem rc5_dpairsCount_eq_card_dpairs (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = (rc5_dpairs 𝒜 ℬ).card := rfl


theorem rc5_dbl_injOn_dpairs (𝒜 ℬ : Finset (Finset α)) :
    Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) (rc5_dpairs 𝒜 ℬ) :=
  dbl_injective.injOn


theorem rc5_boxDoubled_eq_image (𝒜 ℬ : Finset (Finset α)) :
    boxDoubled 𝒜 ℬ = (rc5_dpairs 𝒜 ℬ).image (fun p => dbl p.1 p.2) := rfl


theorem rc5_card_boxDoubled_eq_card_dpairs (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = (rc5_dpairs 𝒜 ℬ).card := by
  rw [rc5_boxDoubled_eq_image, Finset.card_image_of_injOn (rc5_dbl_injOn_dpairs 𝒜 ℬ)]


theorem rc5_doubled_box_count (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
  rw [rc5_card_boxDoubled_eq_card_dpairs, rc5_dpairsCount_eq_card_dpairs]


theorem rc5_doubled_box_count_chain (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ ∧
      dpairsCount 𝒜 ℬ = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card :=
  ⟨rc5_doubled_box_count 𝒜 ℬ, rfl⟩


theorem rc5_card_boxDoubled_eq_card_filter (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card :=
  (rc5_doubled_box_count 𝒜 ℬ).trans (rc5_dpairsCount_eq_card_dpairs 𝒜 ℬ)


theorem rc5_dbl_mem_boxDoubled {𝒜 ℬ : Finset (Finset α)} {p : Finset α × Finset α}
    (hp : p ∈ rc5_dpairs 𝒜 ℬ) : dbl p.1 p.2 ∈ boxDoubled 𝒜 ℬ := by
  rw [rc5_mem_dpairs] at hp
  obtain ⟨⟨hS, hT⟩, hd⟩ := hp
  rw [mem_boxDoubled]
  exact ⟨p.1, hS, p.2, hT, hd, rfl⟩


theorem rc5_card_boxDoubled_eq_card_dpairs_bij (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = (rc5_dpairs 𝒜 ℬ).card := by
  symm
  refine Finset.card_bij (fun p _ => dbl p.1 p.2) (fun p hp => rc5_dbl_mem_boxDoubled hp)
    (fun p hp q hq h => dbl_injective h) ?_
  intro U hU
  rw [mem_boxDoubled] at hU
  obtain ⟨S, hS, T, hT, hd, hdbl⟩ := hU
  exact ⟨(S, T), by rw [rc5_mem_dpairs]; exact ⟨⟨hS, hT⟩, hd⟩, hdbl⟩


theorem rc5_union_not_injOn_dpairs (a : α) :
    ¬ Set.InjOn (fun p : Finset α × Finset α => p.1 ∪ p.2)
        (rc5_dpairs ({∅, {a}} : Finset (Finset α)) {∅, {a}}) := by
  intro hinj
  have hp1 : (({a}, ∅) : Finset α × Finset α) ∈
      rc5_dpairs ({∅, {a}} : Finset (Finset α)) {∅, {a}} := by
    rw [rc5_mem_dpairs]
    exact ⟨⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      Finset.mem_insert_self _ _⟩, by simp⟩
  have hp2 : ((∅, {a}) : Finset α × Finset α) ∈
      rc5_dpairs ({∅, {a}} : Finset (Finset α)) {∅, {a}} := by
    rw [rc5_mem_dpairs]
    exact ⟨⟨Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, by simp⟩
  have hunion : (({a}, ∅) : Finset α × Finset α).1 ∪ (({a}, ∅) : Finset α × Finset α).2
      = ((∅, {a}) : Finset α × Finset α).1 ∪ ((∅, {a}) : Finset α × Finset α).2 := by simp
  have heq := hinj hp1 hp2 hunion
  have hne : (({a}, ∅) : Finset α × Finset α) ≠ ((∅, {a}) : Finset α × Finset α) := by
    intro h
    exact (Finset.singleton_ne_empty a) (congrArg Prod.fst h)
  exact hne heq


end StatMech.Walls
