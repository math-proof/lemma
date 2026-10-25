/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc71disjpreserving.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.Walls.rc72configpair.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc72_source_card (A B : Finset (ConfigSpace (Fin 2))) :
    (rc72_source A B).card = (rc72_disjOcc A B).card * 2 ^ 2 := by
  rw [rc72_source, Finset.card_product, Finset.card_univ]
  congr 1


theorem rc72_graftSwap_mem_reachCells (A B : Finset (ConfigSpace (Fin 2)))
    {ω₁ ω₂ : ConfigSpace (Fin 2)} (hω₁ : ω₁ ∈ rc72_disjOcc A B)
    {L : Finset (Fin 2)} (hL : L ∈ rc72_wits A B ω₁)
    (hAB : (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B) :
    graftSwap L (ω₁, ω₂) ∈ rc72_reachCells A B := by
  rw [rc72_reachCells, Finset.mem_filter]
  refine ⟨?_, hAB⟩
  rw [Finset.mem_biUnion]
  exact ⟨ω₁, hω₁, Finset.mem_biUnion.mpr ⟨ω₂, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨L, hL, rfl⟩⟩⟩

open Classical in


theorem rc72_source_card_le_reach_of_injection (A B : Finset (ConfigSpace (Fin 2)))
    (Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2))
    (hwit : ∀ ω₁ ∈ rc72_disjOcc A B, ∀ ω₂ : ConfigSpace (Fin 2), Lc ω₁ ω₂ ∈ rc72_wits A B ω₁)
    (hAB : ∀ ω₁ ∈ rc72_disjOcc A B, ∀ ω₂ : ConfigSpace (Fin 2),
        (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ A ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ B)
    (hinj : Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) =>
        graftSwap (Lc p.1 p.2) p) (rc72_source A B)) :
    2 ^ 2 * (rc72_disjOcc A B).card ≤ (rc72_reachCells A B).card := by
  
  have hmaps : ∀ p ∈ rc72_source A B,
      (fun q : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) => graftSwap (Lc q.1 q.2) q) p
        ∈ rc72_reachCells A B := by
    rintro ⟨ω₁, ω₂⟩ hp
    rw [rc72_source, Finset.mem_product] at hp
    obtain ⟨hω₁, _⟩ := hp
    exact rc72_graftSwap_mem_reachCells A B hω₁ (hwit ω₁ hω₁ ω₂) (hAB ω₁ hω₁ ω₂)
  have := Finset.card_le_card_of_injOn
    (f := fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) => graftSwap (Lc p.1 p.2) p)
    hmaps hinj
  rwa [rc72_source_card, mul_comm] at this

open Classical in
set_option maxRecDepth 8000 in


theorem rc72_no_graftSwap_injection_fin2 :
    ¬ ∃ Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2),
        (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2),
            Lc ω₁ ω₂ ∈ rc72_wits rc72_wA rc72_wB ω₁) ∧
        (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2),
            (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ rc72_wA
              ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ rc72_wB) ∧
        Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) =>
            graftSwap (Lc p.1 p.2) p) (rc72_source rc72_wA rc72_wB) := by
  rintro ⟨Lc, hwit, hAB, hinj⟩
  have hbound := rc72_source_card_le_reach_of_injection rc72_wA rc72_wB Lc hwit hAB hinj
  obtain ⟨hdisj, _, hreach⟩ := rc72_witness_counts
  rw [hdisj, hreach] at hbound
  
  omega


open Classical in


theorem rc72_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc71_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 8000 in


theorem rc72_status :
    
    (∀ (m : ℕ) (L : Finset (Fin m)), Function.Bijective (graftSwap L)) ∧
    (∀ (m : ℕ) (L : Finset (Fin m)) (p : ConfigSpace (Fin m) × ConfigSpace (Fin m)),
        (Finset.univ.filter (fun i => (graftSwap L p).1 i = true)).card
            + (Finset.univ.filter (fun i => (graftSwap L p).2 i = true)).card
          = (Finset.univ.filter (fun i => p.1 i = true)).card
            + (Finset.univ.filter (fun i => p.2 i = true)).card) ∧
    
    (∀ (m : ℕ) (A B : Set (ConfigSpace (Fin m))) (K L : Finset (Fin m)), Disjoint K L →
        ∀ (ω₁ ω₂ : ConfigSpace (Fin m)),
        OccursOn A (K : Set (Fin m)) ω₁ → OccursOn B (L : Set (Fin m)) ω₁ →
        (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B) ∧
    
    ((rc72_reachCells rc72_wA rc72_wB).card
        < 2 ^ 2 * (rc72_disjOcc rc72_wA rc72_wB).card) ∧
    
    (¬ ∃ Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2),
        (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2),
            Lc ω₁ ω₂ ∈ rc72_wits rc72_wA rc72_wB ω₁) ∧
        (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2),
            (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ rc72_wA
              ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ rc72_wB) ∧
        Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) =>
            graftSwap (Lc p.1 p.2) p) (rc72_source rc72_wA rc72_wB)) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _m L => graftSwap_bijective L,
   fun _m L p => graftSwap_jointCount L p,
   fun _m A B _K _L hKL ω₁ ω₂ hA hB => graftSwap_mapsInto_of_witness A B hKL ω₁ ω₂ hA hB,
   rc72_graftSwap_reach_cap_fin2,
   rc72_no_graftSwap_injection_fin2,
   rc72_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
