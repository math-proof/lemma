/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem r2k_swapInjection_of_perOrbitCard (A B : Set (ConfigSpace α))
    (hpo : PerOrbitCard A B) : r2k_SwapInjection A B := by
  classical
  set Dom := {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} with hDom
  set r : Dom → (ConfigSpace α × ConfigSpace α) → Prop :=
    fun p q => sameOrbit p.val q ∧ q.1 ∈ A ∧ q.2 ∈ B with hr
  
  have key : ∃ f : Dom → (ConfigSpace α × ConfigSpace α),
      Function.Injective f ∧ ∀ x, r x (f x) := by
    rw [← Fintype.all_card_le_filter_rel_iff_exists_injective r]
    intro Aset
    set K := Aset.image (fun p : Dom => orbitKey p.val) with hK
    have hfib : #Aset = ∑ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k)) := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp; exact Finset.mem_image_of_mem _ hp
    rw [hfib]
    
    have hkstep : ∀ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k)) ≤ #(imgOrbit A B k) := by
      intro k _
      refine le_trans ?_ (hpo k)
      apply Finset.card_le_card_of_injOn (fun p => p.val)
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        simp only [boxOrbit, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨p.property, hp.2⟩
      · intro a _ b _ hab; exact Subtype.ext hab
    calc ∑ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k))
        ≤ ∑ k ∈ K, #(imgOrbit A B k) := Finset.sum_le_sum hkstep
      _ = #(K.biUnion (fun k => imgOrbit A B k)) := by
          rw [Finset.card_biUnion]
          intro k1 _ k2 _ hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro q hq1 hq2
          simp only [imgOrbit, Finset.mem_filter] at hq1 hq2
          exact hne (hq1.2.2.2 ▸ hq2.2.2.2)
      _ ≤ #{b | ∃ a ∈ Aset, r a b} := by
          apply Finset.card_le_card
          intro q hq
          rw [Finset.mem_biUnion] at hq
          obtain ⟨k, hkK, hqimg⟩ := hq
          simp only [imgOrbit, Finset.mem_filter] at hqimg
          rw [hK, Finset.mem_image] at hkK
          obtain ⟨p, hpA, hpk⟩ := hkK
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ q, p, hpA, ?_, hqimg.2.1, hqimg.2.2.1⟩
          rw [sameOrbit_iff_orbitKey, hpk, ← hqimg.2.2.2]
  
  obtain ⟨f, hfinj, hfr⟩ := key
  set σ : ConfigSpace α × ConfigSpace α → (α → Bool) :=
    fun p => if hp : p.1 ∈ disjointOccurrence A B then
      (fun a => decide ((f ⟨p, hp⟩).1 a ≠ p.1 a)) else (fun _ => false) with hσ
  
  have hσbox : ∀ p (hp : p.1 ∈ disjointOccurrence A B), swapPair σ p = f ⟨p, hp⟩ := by
    intro p hp
    have hso : sameOrbit p (f ⟨p, hp⟩) := (hfr ⟨p, hp⟩).1
    have heq : swapPair (fun _ => fun a => decide ((f ⟨p, hp⟩).1 a ≠ p.1 a)) p = f ⟨p, hp⟩ :=
      (swapPair_eq_of_sameOrbit p (f ⟨p, hp⟩) hso).symm
    rw [← heq]
    simp only [swapPair, hσ, dif_pos hp]
  refine ⟨σ, ?_, ?_⟩
  · 
    intro p hp
    have hmem := (hfr ⟨p, hp⟩).2
    rw [hσbox p hp]
    exact ⟨hmem.1, hmem.2⟩
  · 
    intro p hp q hq heq
    rw [Set.mem_setOf_eq] at hp hq
    rw [hσbox p hp, hσbox q hq] at heq
    have : (⟨p, hp⟩ : Dom) = ⟨q, hq⟩ := hfinj heq
    exact Subtype.ext_iff.mp this


theorem perOrbitCard_of_swapInjection (A B : Set (ConfigSpace α))
    (hSI : r2k_SwapInjection A B) : PerOrbitCard A B := by
  classical
  obtain ⟨σ, hmem, hinj⟩ := hSI
  intro k
  apply Finset.card_le_card_of_injOn (swapPair σ)
  · intro p hp
    rw [Finset.mem_coe, boxOrbit, Finset.mem_filter] at hp
    obtain ⟨_, hpbox, hpk⟩ := hp
    have hm := hmem p hpbox
    simp only [imgOrbit, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hm.1, hm.2, by rw [orbitKey_swapPair]; exact hpk⟩
  · intro p hp q hq hpq
    rw [Finset.mem_coe, boxOrbit, Finset.mem_filter] at hp hq
    exact hinj hp.2.1 hq.2.1 hpq


theorem r2k_swapInjection_iff_perOrbitCard (A B : Set (ConfigSpace α)) :
    r2k_SwapInjection A B ↔ PerOrbitCard A B :=
  ⟨perOrbitCard_of_swapInjection A B, r2k_swapInjection_of_perOrbitCard A B⟩


theorem reimer_wprob_of_perOrbitCard (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (hpo : PerOrbitCard A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  r2k_reimer_wprob_of_swapInjection φ hφ0 hφ1 (r2k_swapInjection_of_perOrbitCard A B hpo)


theorem perOrbitCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    PerOrbitCard A B :=
  perOrbitCard_of_swapInjection A B (r2k_swapInjection_of_disjoint_support hA hB hST)


theorem perOrbitCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : PerOrbitCard A B :=
  perOrbitCard_of_swapInjection A B (r2k_swapInjection_of_box_empty hbox)


theorem perOrbitCard_rbi : PerOrbitCard rbi_A rbi_B :=
  perOrbitCard_of_swapInjection rbi_A rbi_B r2k_swapInjection_rbi


end StatMech
