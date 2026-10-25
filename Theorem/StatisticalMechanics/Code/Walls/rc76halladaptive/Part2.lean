/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Def.StatisticalMechanics.Code.Walls.rc76halladaptive.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc76_mem_reachNbhd (A B : Finset (ConfigSpace (Fin n)))
    (p q : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    q ∈ rc76_reachNbhd A B p ↔ (q.1 ∈ A ∧ q.2 ∈ B) ∧ ∃ S : Finset (Fin n), swapSet S p = q := by
  classical
  unfold rc76_reachNbhd
  rw [Finset.mem_filter, Finset.mem_product]


theorem rc76_hall_iff_plan (A B : Finset (ConfigSpace (Fin n)))
    (src : Finset (ConfigSpace (Fin n) × ConfigSpace (Fin n))) :
    (∀ T : Finset (ConfigSpace (Fin n) × ConfigSpace (Fin n)), T ⊆ src →
        T.card ≤ (T.biUnion (fun p => rc76_reachNbhd A B p)).card) ↔
      ∃ f : (ConfigSpace (Fin n) × ConfigSpace (Fin n)) → (ConfigSpace (Fin n) × ConfigSpace (Fin n)),
        Set.InjOn f src ∧ ∀ p ∈ src, f p ∈ rc76_reachNbhd A B p := by
  classical
  
  have hHall := Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun p : (↥src) => rc76_reachNbhd A B (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)))
  
  have hbi : ∀ s : Finset (↥src),
      (s.map (Function.Embedding.subtype _)).biUnion (fun p => rc76_reachNbhd A B p)
        = s.biUnion (fun p => rc76_reachNbhd A B (p : _)) := by
    intro s
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, hq⟩; exact ⟨y, hy, hq⟩
    · rintro ⟨y, hy, hq⟩; exact ⟨(y : _), ⟨y, hy, rfl⟩, hq⟩
  constructor
  · intro hmar
    
    have hsub : ∀ s : Finset (↥src), s.card ≤
        (s.biUnion (fun p => rc76_reachNbhd A B (p : _))).card := by
      intro s
      have himg := hmar (s.map (Function.Embedding.subtype _))
        (by intro x hx; simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
            obtain ⟨y, _, rfl⟩ := hx; exact y.2)
      rw [Finset.card_map, hbi s] at himg
      exact himg
    obtain ⟨f, hfinj, hfmem⟩ := hHall.mp hsub
    
    classical
    refine ⟨fun p => if hp : p ∈ src then f ⟨p, hp⟩ else p, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_coe] at hx hy
      simp only [dif_pos hx, dif_pos hy] at hxy
      have := hfinj hxy
      exact congrArg Subtype.val this
    · intro p hp
      simp only [dif_pos hp]
      exact hfmem ⟨p, hp⟩
  · rintro ⟨f, hinj, hmem⟩
    
    
    intro T hT
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      rw [Finset.mem_coe] at hp
      rw [Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨p, hp, hmem p (hT hp)⟩
    · intro x hx y hy hxy
      exact hinj (Finset.mem_coe.mpr (hT hx)) (Finset.mem_coe.mpr (hT hy)) hxy


end StatMech.Walls
