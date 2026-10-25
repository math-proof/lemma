/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11bkriffincinc
import Theorem.StatisticalMechanics.Code.Walls.rc11boxsuppupper
import Theorem.StatisticalMechanics.Code.Walls.rc11reflinterstructure
import Theorem.StatisticalMechanics.Code.Walls.rc11doublecoverrepresentation
import Theorem.StatisticalMechanics.Code.Walls.rc11compressionengine
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc11_boxSupp_upper_split (𝒜 ℬ : Finset (Finset α))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) (S : Finset α) :
    S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ T ⊆ S, T ∈ 𝒜 ∧ S \ T ∈ ℬ := by
  rw [rc11_mem_boxSupp]
  constructor
  · rintro ⟨K, L, hKL, hKS, hLS, hK, hL⟩
    refine ⟨K, hKS, hK, ?_⟩
    apply hℬ _ hL
    rw [Finset.le_iff_subset]
    intro x hx
    rw [Finset.mem_sdiff]
    exact ⟨hLS hx, fun hxK => (Finset.disjoint_left.mp hKL hxK) hx⟩
  · rintro ⟨T, hTS, hT, hST⟩
    exact ⟨T, S \ T, Finset.disjoint_sdiff, hTS, Finset.sdiff_subset, hT, hST⟩

open Classical in


theorem rc11_boxSupp_subset_left (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) :
    rc10_boxSupp 𝒜 ℬ ⊆ 𝒜 := by
  intro S hS
  rw [rc11_mem_boxSupp] at hS
  obtain ⟨K, _, _, hKS, _, hK, _⟩ := hS
  exact h𝒜 (Finset.coe_subset.mpr hKS) hK

open Classical in


theorem rc11_boxSupp_subset_right (𝒜 ℬ : Finset (Finset α))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    rc10_boxSupp 𝒜 ℬ ⊆ ℬ := by
  intro S hS
  rw [rc11_mem_boxSupp] at hS
  obtain ⟨K, L, _, _, hLS, _, hL⟩ := hS
  exact hℬ (Finset.coe_subset.mpr hLS) hL


open Classical in


theorem rc11_boxSupp_eq_reflInter_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    rc10_boxSupp 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
  ext S
  rw [rc10_boxSupp, rc10_reflInter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hS : S = ∅ := Finset.eq_empty_of_forall_notMem fun x => x.elim0
  subst hS
  constructor
  · rintro ⟨K, L, _, hKS, hLS, hK, hL⟩
    obtain rfl := Finset.subset_empty.mp hKS
    obtain rfl := Finset.subset_empty.mp hLS
    exact ⟨hK, by simpa using hL⟩
  · rintro ⟨hSA, hSB⟩
    exact ⟨∅, ∅, disjoint_empty_left _, Finset.empty_subset _, Finset.empty_subset _, hSA,
      by simpa using hSB⟩

open Classical in


theorem rc11_bkr_fin0 (𝒜 ℬ : Finset (Finset (Fin 0)))
    (_h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin 0))))
    (_hℬ : IsUpperSet (ℬ : Set (Finset (Fin 0)))) :
    #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc11_boxSupp_eq_reflInter_fin0]


open Classical in


theorem rc11_bkr_fin1 (𝒜 ℬ : Finset (Finset (Fin 1)))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin 1))))
    (hℬ : IsUpperSet (ℬ : Set (Finset (Fin 1)))) :
    #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  set A := familyEvent 𝒜 with hA
  set B := familyEvent ℬ with hB
  have hAinc : IsIncreasing A := by
    intro ω ω' hωω' hω
    simp only [hA, mem_familyEvent] at hω ⊢
    exact h𝒜 (Finset.coe_subset.mpr (cfgSupport_subset_of_le hωω')) hω
  have hBinc : IsIncreasing B := by
    intro ω ω' hωω' hω
    simp only [hB, mem_familyEvent] at hω ⊢
    exact hℬ (Finset.coe_subset.mpr (cfgSupport_subset_of_le hωω')) hω
  have hdef := rc9_deficit_one A B
  have hEA : eventFamily A = 𝒜 := rc10_eventFamily_familyEvent 𝒜
  have hEB : eventFamily B = ℬ := rc10_eventFamily_familyEvent ℬ
  rw [rc5_deficit, rc10_card_box_eq A B hAinc hBinc, rc10_card_reflInter_eq A B, hEA, hEB] at hdef
  have : (#(rc10_boxSupp 𝒜 ℬ) : ℤ) ≤ #(rc10_reflInter 𝒜 ℬ) := by linarith [hdef]
  exact_mod_cast this


open Classical in


theorem rc11_boxSupp_reflInter_right_univ (𝒜 : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) :
    rc10_boxSupp 𝒜 univ = 𝒜 ∧ rc10_reflInter 𝒜 univ = 𝒜 := by
  refine ⟨?_, ?_⟩
  · ext S; rw [rc11_mem_boxSupp]
    constructor
    · rintro ⟨K, _, _, hKS, _, hK, _⟩
      exact h𝒜 (Finset.coe_subset.mpr hKS) hK
    · intro hS
      exact ⟨S, ∅, Finset.disjoint_empty_right _, Finset.Subset.refl S, Finset.empty_subset _, hS,
        Finset.mem_univ _⟩
  · ext S; rw [rc11_mem_reflInter]; simp [Finset.mem_univ]

open Classical in


theorem rc11_bkr_right_univ (𝒜 : Finset (Finset α)) (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) :
    #(rc10_boxSupp 𝒜 univ) ≤ #(rc10_reflInter 𝒜 univ) := by
  obtain ⟨hbox, hrefl⟩ := rc11_boxSupp_reflInter_right_univ 𝒜 h𝒜
  rw [hbox, hrefl]

open Classical in


theorem rc11_boxSupp_left_univ (ℬ : Finset (Finset α)) (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    rc10_boxSupp univ ℬ = ℬ := by
  ext S; rw [rc11_mem_boxSupp]
  constructor
  · rintro ⟨_, L, _, _, hLS, _, hL⟩
    exact hℬ (Finset.coe_subset.mpr hLS) hL
  · intro hS
    exact ⟨∅, S, Finset.disjoint_empty_left _, Finset.empty_subset _, Finset.Subset.refl S,
      Finset.mem_univ _, hS⟩

open Classical in


theorem rc11_card_reflInter_left_univ (ℬ : Finset (Finset α)) :
    #(rc10_reflInter univ ℬ) = #ℬ := by
  rw [rc11_reflInter_eq_inter, Finset.univ_inter]
  unfold rc11_reflPull
  apply Finset.card_bij (fun S _ => Sᶜ)
  · intro S hS; rw [Finset.mem_filter] at hS; exact hS.2
  · intro a _ b _ hab; simpa using congrArg compl hab
  · intro T hT
    exact ⟨Tᶜ, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rwa [compl_compl]⟩,
      compl_compl T⟩

open Classical in


theorem rc11_bkr_left_univ (ℬ : Finset (Finset α)) (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    #(rc10_boxSupp univ ℬ) ≤ #(rc10_reflInter univ ℬ) := by
  rw [rc11_boxSupp_left_univ ℬ hℬ, rc11_card_reflInter_left_univ ℬ]


end StatMech.Walls
