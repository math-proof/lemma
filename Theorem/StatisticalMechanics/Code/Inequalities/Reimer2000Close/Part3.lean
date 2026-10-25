/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
import Def.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part3
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [DecidableEq α] in


theorem r2k_weightInjection_of_swapInjection {A B : Set (ConfigSpace α)}
    (hSI : r2k_SwapInjection A B) : rpw_WeightInjection A B := by
  obtain ⟨σ, hmem, hinj⟩ := hSI
  refine ⟨swapPair σ, hmem, ?_, hinj⟩
  intro φ p _
  simp only [swapPair_fst, swapPair_snd]
  exact swapPair_weight φ (σ p) p.1 p.2


theorem r2k_reimer_wprob_of_swapInjection (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (hSI : r2k_SwapInjection A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  rpw_reimer_wprob_of_weightInjection φ hφ0 hφ1 (r2k_weightInjection_of_swapInjection hSI)


omit [Fintype α] [DecidableEq α] in


theorem r2k_swapPair_const_injective (S₀ : α → Bool) :
    Function.Injective (swapPair (fun _ => S₀) : ConfigSpace α × ConfigSpace α → _) := by
  intro p q h
  simp only [swapPair] at h
  have h1 : swapGlue S₀ p.1 p.2 = swapGlue S₀ q.1 q.2 := congrArg Prod.fst h
  have h2 : swapGlue S₀ p.2 p.1 = swapGlue S₀ q.2 q.1 := congrArg Prod.snd h
  ext a
  · rw [show p.1 = swapGlue S₀ (swapGlue S₀ p.1 p.2) (swapGlue S₀ p.2 p.1) from
      (swapGlue_swapGlue_left S₀ p.1 p.2).symm, h1, h2, swapGlue_swapGlue_left S₀ q.1 q.2]
  · rw [show p.2 = swapGlue S₀ (swapGlue S₀ p.2 p.1) (swapGlue S₀ p.1 p.2) from
      (swapGlue_swapGlue_right S₀ p.1 p.2).symm, h1, h2, swapGlue_swapGlue_right S₀ q.1 q.2]


omit [Fintype α] in


theorem r2k_swapInjection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    r2k_SwapInjection A B := by
  classical
  
  refine ⟨fun _ => fun a => decide (a ∉ S), ?_,
    (r2k_swapPair_const_injective (fun a => decide (a ∉ S))).injOn⟩
  intro p hp
  
  have hagA : agreeOn (↑S : Set α) p.1 (swapGlue (fun a => decide (a ∉ S)) p.1 p.2) := by
    intro a ha
    simp only [Finset.mem_coe] at ha
    have : ¬ a ∉ S := not_not.mpr ha
    simp only [swapGlue_apply, this, decide_false, Bool.false_eq_true, if_false]
  
  have hagB : agreeOn (↑T : Set α) p.1 (swapGlue (fun a => decide (a ∉ S)) p.2 p.1) := by
    intro a ha
    simp only [Finset.mem_coe] at ha
    have haS : a ∉ S := fun h => (Finset.disjoint_left.mp hST) h ha
    have : decide (a ∉ S) = true := decide_eq_true haS
    simp only [swapGlue_apply, this, if_true]
  refine ⟨?_, ?_⟩
  · 
    have hp1A : p.1 ∈ A := (disjointOccurrence_subset_inter A B hp).1
    exact (hA p.1 _ hagA).mp hp1A
  · 
    have hp1B : p.1 ∈ B := (disjointOccurrence_subset_inter A B hp).2
    exact (hB p.1 _ hagB).mp hp1B


omit [Fintype α] [DecidableEq α] in


theorem r2k_swapInjection_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : r2k_SwapInjection A B := by
  refine ⟨fun _ => fun _ => false, ?_, ?_⟩
  · intro p hp; rw [hbox] at hp; exact absurd hp (Set.notMem_empty p.1)
  · intro p hp; rw [Set.mem_setOf_eq, hbox] at hp; exact absurd hp (Set.notMem_empty p.1)


end StatMech
