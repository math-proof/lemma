/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc86consolidation
import Def.StatisticalMechanics.Code.Walls.rb3reimerclose.Part3
open Finset
open scoped BigOperators NNReal


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unusedSimpArgs false


lemma rb3_body_apply {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) (i : Fin n) :
    rb3_body 𝒜 ℬ (rb3_toB S) i =
      (if i ∈ rb3_witK 𝒜 ℬ S then rb3_toB S i else !(rb3_toB S i)) := by
  classical
  simp only [rb3_body, rb3_ofB_toB, rb3_toB, rc36_R0, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff, Finset.mem_compl]
  by_cases hK : i ∈ rb3_witK 𝒜 ℬ S <;>
    by_cases hS : i ∈ S <;> simp [hK, hS]

open Classical in


lemma rb3_inRed_iff {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) (x : rbt_Q n) :
    rbt_inRed (rb3_body 𝒜 ℬ (rb3_toB S)) (rb3_toB S) x ↔
      (rb3_ofB x) ∩ (rb3_witK 𝒜 ℬ S) = S ∩ (rb3_witK 𝒜 ℬ S) := by
  rw [rb3_inter_eq_iff_agree, rb3_toB_ofB]
  rw [rbt_inRed, rbt_inCube]
  constructor
  · intro h i hiK
    rcases h i with hc | hy
    · rw [hc, rb3_body_apply, if_pos hiK]
    · exact hy
  · intro h i
    by_cases hiK : i ∈ rb3_witK 𝒜 ℬ S
    · exact Or.inr (h i hiK)
    · 
      by_cases hxi : x i = rb3_toB S i
      · exact Or.inr hxi
      · left
        rw [rb3_body_apply, if_neg hiK]
        cases hx : x i <;> cases hSi : rb3_toB S i <;> simp_all

open Classical in


lemma rb3_inYellow_iff {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) (x : rbt_Q n) :
    rbt_inYellow (rb3_body 𝒜 ℬ (rb3_toB S)) (rb3_toB S) x ↔
      (rb3_ofB x)ᶜ ∩ (rb3_witK 𝒜 ℬ S)ᶜ = S ∩ (rb3_witK 𝒜 ℬ S)ᶜ := by
  rw [rb3_inter_eq_iff_agree]
  
  have hcompl : ∀ i, rb3_toB (rb3_ofB x)ᶜ i = !(x i) := by
    intro i
    have := rb3_toB_compl (rb3_ofB x)
    have h2 := congrFun this i
    rw [rbt_antipode, rb3_toB_ofB] at h2
    rw [← h2]
  rw [rbt_inYellow, rbt_inCube]
  constructor
  · intro h i hiKc
    rw [hcompl i]
    rcases h i with hc | hy
    · 
      rw [hc, rb3_body_apply]
      
      have hiK : i ∉ rb3_witK 𝒜 ℬ S := by simpa [Finset.mem_compl] using hiKc
      rw [if_neg hiK]
      cases hSi : rb3_toB S i <;> simp_all
    · 
      rw [rbt_antipode] at hy
      rw [hy]; cases hSi : rb3_toB S i <;> simp_all
  · intro h i
    by_cases hiK : i ∈ rb3_witK 𝒜 ℬ S
    · 
      by_cases hxi : x i = rb3_toB S i
      · left; rw [hxi, rb3_body_apply, if_pos hiK]
      · right; rw [rbt_antipode]; cases hx : x i <;> cases hS : rb3_toB S i <;> simp_all
    · 
      have hiKc : i ∈ (rb3_witK 𝒜 ℬ S)ᶜ := by simpa [Finset.mem_compl] using hiK
      have := h i hiKc
      rw [hcompl i] at this
      
      right
      rw [rbt_antipode]
      cases hx : x i <;> cases hS : rb3_toB S i <;> simp_all


open Classical in


lemma rb3_red_mem_A {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n)))
    {x : rbt_Q n} (hx : x ∈ rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
    rb3_ofB x ∈ 𝒜 := by
  rw [rbt_Red, Finset.mem_filter] at hx
  obtain ⟨y, hyT, hxy⟩ := hx.2
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hyT
  rw [rb3_inRed_iff] at hxy
  exact (rb3_witK_spec 𝒜 ℬ hS).1 _ hxy

open Classical in


lemma rb3_yellow_mem_B {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n)))
    {x : rbt_Q n} (hx : x ∈ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
    (rb3_ofB x)ᶜ ∈ ℬ := by
  rw [rbt_Yellow, Finset.mem_filter] at hx
  obtain ⟨y, hyT, hxy⟩ := hx.2
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hyT
  rw [rb3_inYellow_iff] at hxy
  exact (rb3_witK_spec 𝒜 ℬ hS).2 _ hxy

open Classical in


lemma rb3_redYellow_ofB_mem_reflInter {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n)))
    {x : rbt_Q n}
    (hx : x ∈ rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)
        ∩ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
    rb3_ofB x ∈ rc10_reflInter 𝒜 ℬ := by
  rw [Finset.mem_inter] at hx
  rw [rc20_mem_reflInter]
  exact ⟨rb3_red_mem_A 𝒜 ℬ hx.1, rb3_yellow_mem_B 𝒜 ℬ hx.2⟩

open Classical in


lemma rb3_card_redYellow_le_reflInter {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) :
    (rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)
        ∩ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)).card
      ≤ (rc10_reflInter 𝒜 ℬ).card := by
  apply Finset.card_le_card_of_injOn rb3_ofB
  · intro x hx
    exact rb3_redYellow_ofB_mem_reflInter 𝒜 ℬ hx
  · intro a _ b _ hab
    have := congrArg rb3_toB hab
    rwa [rb3_toB_ofB, rb3_toB_ofB] at this

open Classical in


lemma rb3_card_tips {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) :
    ((rc20_famCylBox 𝒜 ℬ).image rb3_toB).card = (rc20_famCylBox 𝒜 ℬ).card :=
  Finset.card_image_of_injective _ rb3_toB_injective

open Classical in


theorem rb3_famCylBox_le_reflInter {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) :
    (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card := by
  rw [← rb3_card_tips 𝒜 ℬ]
  calc ((rc20_famCylBox 𝒜 ℬ).image rb3_toB).card
      ≤ (rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)
          ∩ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)).card :=
        rb2_butterfly_thm n (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)
    _ ≤ (rc10_reflInter 𝒜 ℬ).card := rb3_card_redYellow_le_reflInter 𝒜 ℬ


theorem rb3_famCylBoxResidue : StatMech.Walls.rc20_FamCylBoxResidue :=
  fun _ 𝒜 ℬ => rb3_famCylBox_le_reflInter 𝒜 ℬ


theorem rb3_reimerWprobCore : StatMech.ReimerWprobCore :=
  StatMech.rc84_residue_is_famCylBox rb3_famCylBoxResidue


theorem rb3_thm_reimer {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    (A B : Set (StatMech.ConfigSpace E)) :
    (StatMech.bernoulliProductMeasure (E := E) p hp).real (StatMech.disjointOccurrence A B)
      ≤ (StatMech.bernoulliProductMeasure (E := E) p hp).real A
        * (StatMech.bernoulliProductMeasure (E := E) p hp).real B :=
  StatMech.reimer_inequality_of_core rb3_reimerWprobCore hp A B

end StatMech.Walls.Reimer
