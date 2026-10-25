/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc10_occursOn_iff_fin {A : Set (ConfigSpace α)} (hA : IsIncreasing A) (K : Finset α)
    (ω : ConfigSpace α) (hK : K ⊆ cfgSupport ω) : OccursOn A (↑K) ω ↔ supportCfg K ∈ A := by
  constructor
  · intro h
    apply h; intro e he; simp only [Finset.mem_coe] at he
    have : ω e = true := by rw [← mem_cfgSupport]; exact hK he
    simp only [supportCfg_apply, this]; simp [he]
  · intro h ω' hω'
    refine hA (fun a => ?_) h
    by_cases ha : a ∈ K
    · have : ω a = true := by rw [← mem_cfgSupport]; exact hK ha
      have hω'a : ω' a = ω a := hω' a (by simp [ha])
      simp only [supportCfg_apply, ha, decide_true]; rw [hω'a, this]
    · simp only [supportCfg_apply, ha, decide_false]; exact Bool.false_le _

open Classical in


theorem rc10_occursOn_restrict_mem {A : Set (ConfigSpace α)} (Kset : Set α) (ω : ConfigSpace α)
    (h : OccursOn A Kset ω) :
    supportCfg (cfgSupport ω ∩ {a | a ∈ Kset}.toFinset) ∈ A := by
  apply h
  intro e he
  simp only [supportCfg_apply, Finset.mem_inter, mem_cfgSupport, Set.mem_toFinset,
    Set.mem_setOf_eq]
  by_cases hω : ω e = true
  · simp [hω, he]
  · simp only [Bool.not_eq_true] at hω; rw [hω]; simp

open Classical in


theorem rc10_box_increasing_iff {A B : Set (ConfigSpace α)} (hA : IsIncreasing A)
    (hB : IsIncreasing B) (ω : ConfigSpace α) :
    ω ∈ disjointOccurrence A B ↔
      ∃ K L : Finset α, Disjoint K L ∧ K ⊆ cfgSupport ω ∧ L ⊆ cfgSupport ω ∧
        supportCfg K ∈ A ∧ supportCfg L ∈ B := by
  constructor
  · rintro ⟨Kset, Lset, hKL, hAK, hBL⟩
    refine ⟨cfgSupport ω ∩ {a | a ∈ Kset}.toFinset, cfgSupport ω ∩ {a | a ∈ Lset}.toFinset, ?_,
            Finset.inter_subset_left, Finset.inter_subset_left,
            rc10_occursOn_restrict_mem Kset ω hAK, rc10_occursOn_restrict_mem Lset ω hBL⟩
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_inter, Set.mem_toFinset, Set.mem_setOf_eq] at ha hb
    exact (Set.disjoint_left.mp hKL ha.2) hb.2
  · rintro ⟨K, L, hKL, hKsub, hLsub, hKA, hLB⟩
    refine ⟨↑K, ↑L, ?_, ?_, ?_⟩
    · rwa [Finset.disjoint_coe]
    · rw [rc10_occursOn_iff_fin hA K ω hKsub]; exact hKA
    · rw [rc10_occursOn_iff_fin hB L ω hLsub]; exact hLB


theorem rc10_cfgSupport_compl (ω : ConfigSpace α) :
    cfgSupport (rmr_compl ω) = (cfgSupport ω)ᶜ := by
  ext i
  simp only [mem_cfgSupport, rmr_compl, Finset.mem_compl]
  simp [Bool.not_eq_true]

open Classical in


theorem rc10_isUpperSet_eventFamily {A : Set (ConfigSpace α)} (hA : IsIncreasing A) :
    IsUpperSet ((eventFamily A) : Set (Finset α)) := by
  intro S T hST hS
  simp only [Finset.mem_coe, eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hS ⊢
  obtain ⟨ω, hω, hωS⟩ := hS
  refine ⟨supportCfg T, ?_, cfgSupport_supportCfg T⟩
  have hle : ω ≤ supportCfg T := by
    intro a
    rw [← hωS] at hST
    by_cases ha : ω a = true
    · have ha' : a ∈ cfgSupport ω := by rw [mem_cfgSupport]; exact ha
      have haT : a ∈ T := hST ha'
      simp only [supportCfg_apply, haT, decide_true, ha, le_refl]
    · simp only [Bool.not_eq_true] at ha; rw [ha]; exact Bool.false_le _
  exact hA hle hω

open Classical in


theorem rc10_eventFamily_familyEvent (𝒜 : Finset (Finset α)) :
    eventFamily (familyEvent 𝒜) = 𝒜 := by
  ext S
  simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_familyEvent]
  constructor
  · rintro ⟨ω, hω, rfl⟩; exact hω
  · intro hS; exact ⟨supportCfg S, by rw [cfgSupport_supportCfg]; exact hS, cfgSupport_supportCfg S⟩


open Classical in


theorem rc10_card_via_support (P : Finset α → Prop) [DecidablePred P]
    (Q : ConfigSpace α → Prop) [DecidablePred Q] (h : ∀ ω, Q ω ↔ P (cfgSupport ω)) :
    #(univ.filter Q) = #(univ.filter P) := by
  apply Finset.card_bij (fun ω _ => cfgSupport ω)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact (h ω).mp hω
  · intro a _ b _ hab
    have := congrArg supportCfg hab
    rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact ⟨supportCfg S, by rw [h, cfgSupport_supportCfg]; exact hS, cfgSupport_supportCfg S⟩


end StatMech.Walls
