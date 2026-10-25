/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part4
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part4
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc78_filter_subset_srcOrbit (A B : Finset (ConfigSpace (Fin 2)))
    {𝒯 : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))} (h𝒯 : 𝒯 ⊆ rc75_sourceF A B)
    (t : Fin 2 → Bool × Bool) :
    (𝒯.filter (fun p => rc78_colTypeF p = t)) ⊆ rc78_srcOrbit A B t := by
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [rc78_srcOrbit, Finset.mem_filter]
  exact ⟨h𝒯 hp.1, hp.2⟩

open Classical in


theorem rc78_biUnion_nbhd_eq (A B : Finset (ConfigSpace (Fin 2)))
    (𝒯 : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))) :
    𝒯.biUnion (rc78_nbhd A B)
      = (𝒯.image rc78_colTypeF).biUnion (rc78_tgtOrbit A B) := by
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hq⟩
    rw [rc78_nbhd_eq_tgtOrbit] at hq
    exact ⟨rc78_colTypeF p, ⟨p, hp, rfl⟩, hq⟩
  · rintro ⟨t, ⟨p, hp, rfl⟩, hq⟩
    exact ⟨p, hp, by rw [rc78_nbhd_eq_tgtOrbit]; exact hq⟩

open Classical in


theorem rc78_marriage_of_perOrbitDom (A B : Finset (ConfigSpace (Fin 2)))
    (h : rc78_PerOrbitDom A B) : rc78_Marriage A B := by
  intro 𝒯 h𝒯pow
  rw [Finset.mem_powerset] at h𝒯pow
  rw [rc78_biUnion_nbhd_eq]
  set T := 𝒯.image rc78_colTypeF with hT
  
  have hpwd : (↑T : Set (Fin 2 → Bool × Bool)).PairwiseDisjoint (rc78_tgtOrbit A B) := by
    intro t₁ _ t₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    intro q hq₁ hq₂
    rw [rc78_tgtOrbit, Finset.mem_filter] at hq₁ hq₂
    exact hne (hq₁.2.symm.trans hq₂.2)
  
  have hcard_bu : ((T).biUnion (rc78_tgtOrbit A B)).card
      = ∑ t ∈ T, (rc78_tgtOrbit A B t).card :=
    Finset.card_biUnion hpwd
  
  have hpart : 𝒯.card = ∑ t ∈ T, (𝒯.filter (fun p => rc78_colTypeF p = t)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rc78_colTypeF) (t := T)]
    intro p hp
    exact Finset.mem_image_of_mem _ hp
  rw [hpart, hcard_bu]
  apply Finset.sum_le_sum
  intro t _
  calc (𝒯.filter (fun p => rc78_colTypeF p = t)).card
      ≤ (rc78_srcOrbit A B t).card :=
        Finset.card_le_card (rc78_filter_subset_srcOrbit A B h𝒯pow t)
    _ ≤ (rc78_tgtOrbit A B t).card := h t


open Classical in


theorem rc78_existsInjective_of_marriage (A B : Finset (ConfigSpace (Fin 2)))
    (h : rc78_Marriage A B) :
    ∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)),
      Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _) := by
  
  have hHall : ∀ (s : Finset (rc75_sourceF A B)),
      s.card ≤ (s.biUnion (fun p => rc78_nbhd A B (p : _))).card := by
    intro s
    have hmap := h (s.image (Subtype.val))
      (by rw [Finset.mem_powerset]; intro x hx
          rw [Finset.mem_image] at hx; obtain ⟨p, _, rfl⟩ := hx; exact p.2)
    rw [Finset.card_image_of_injective s Subtype.coe_injective] at hmap
    refine hmap.trans (le_of_eq ?_)
    congr 1
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨p, hp, rfl⟩, hq⟩; exact ⟨p, hp, hq⟩
    · rintro ⟨p, hp, hq⟩; exact ⟨(p : _), ⟨p, hp, rfl⟩, hq⟩
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun p : (rc75_sourceF A B) => rc78_nbhd A B (p : _))).mp hHall
  exact ⟨f, hfinj, hfmem⟩


theorem rc78_existsInjective_of_perOrbitDom (A B : Finset (ConfigSpace (Fin 2)))
    (h : rc78_PerOrbitDom A B) :
    ∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)),
      Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _) :=
  rc78_existsInjective_of_marriage A B (rc78_marriage_of_perOrbitDom A B h)


open Classical in


theorem rc78_count_of_existsInjective (A B : Finset (ConfigSpace (Fin 2)))
    (hplan : ∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)),
      Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _)) :
    2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card := by
  obtain ⟨f, hfinj, hfmem⟩ := hplan
  
  let g : (rc75_sourceF A B) → (rc75_prodF A B) := fun p =>
    ⟨f p, by have := hfmem p; rw [rc78_nbhd, Finset.mem_filter] at this; exact this.1⟩
  have hginj : Function.Injective g := by
    intro a b hab
    exact hfinj (congrArg Subtype.val hab)
  have hcard : (rc75_sourceF A B).card ≤ (rc75_prodF A B).card := by
    rw [← Fintype.card_coe (rc75_sourceF A B), ← Fintype.card_coe (rc75_prodF A B)]
    exact Fintype.card_le_of_injective g hginj
  
  rw [rc75_sourceF, Finset.card_product, Finset.card_univ] at hcard
  rw [rc75_prodF, Finset.card_product] at hcard
  have hfull : (Fintype.card (ConfigSpace (Fin 2))) = 4 := by
    simp [ConfigSpace, Fintype.card_bool, Fintype.card_fin]
  rw [hfull] at hcard
  omega


end StatMech.Walls
