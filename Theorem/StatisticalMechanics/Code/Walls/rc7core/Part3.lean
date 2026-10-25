/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6core.Part3
import Def.StatisticalMechanics.Code.Walls.rc7core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section EventCompression

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] in
open Classical in

theorem rc7_mem_downEvent (i : α) (A : Set (ConfigSpace α)) (ω : ConfigSpace α) :
    ω ∈ rc7_downEvent i A ↔
      (if ω i = false then (ω ∈ A ∨ rc7_flip i ω ∈ A) else (ω ∈ A ∧ rc7_flip i ω ∈ A)) :=
  Iff.rfl

open Classical in


theorem rc7_downEvent_card (i : α) (A : Set (ConfigSpace α)) :
    #(univ.filter (fun ω => ω ∈ rc7_downEvent i A)) = #(univ.filter (fun ω => ω ∈ A)) := by
  apply Finset.card_bij (fun ω _ => if ω ∈ A then ω else rc7_flip i ω)
  · intro ω hω
    rw [mem_filter] at hω; obtain ⟨_, hd⟩ := hω; rw [rc7_mem_downEvent] at hd
    rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
    by_cases hA : ω ∈ A
    · simp [hA]
    · simp only [hA, if_false]
      by_cases hi : ω i = false
      · rw [if_pos hi] at hd; rcases hd with h | h; exact absurd h hA; exact h
      · rw [if_neg hi] at hd; exact absurd hd.1 hA
  · intro ω₁ h₁ ω₂ h₂ heq
    rw [mem_filter, rc7_mem_downEvent] at h₁ h₂
    obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂
    have htrue : ∀ ω : ConfigSpace α, (if ω i = false then (ω ∈ A ∨ rc7_flip i ω ∈ A)
        else (ω ∈ A ∧ rc7_flip i ω ∈ A)) → ω ∈ A → ω i ≠ false → rc7_flip i ω ∈ A := by
      intro ω hd hA hi; rw [if_neg hi] at hd; exact hd.2
    by_cases hA1 : ω₁ ∈ A <;> by_cases hA2 : ω₂ ∈ A
    · simpa [hA1, hA2] using heq
    · exfalso; simp only [hA1, if_true, hA2, if_false] at heq
      have hi2 : ω₂ i = false := by
        by_cases hi : ω₂ i = false; exact hi
        rw [if_neg hi] at h₂; exact absurd h₂.1 hA2
      have hi1 : ω₁ i ≠ false := by rw [heq]; simp [hi2]
      have := htrue ω₁ h₁ hA1 hi1
      rw [heq, rc7_flip_involutive i ω₂] at this; exact hA2 this
    · exfalso; simp only [hA1, if_false, hA2, if_true] at heq
      have hi1 : ω₁ i = false := by
        by_cases hi : ω₁ i = false; exact hi
        rw [if_neg hi] at h₁; exact absurd h₁.1 hA1
      have hi2 : ω₂ i ≠ false := by rw [← heq]; simp [hi1]
      have := htrue ω₂ h₂ hA2 hi2
      rw [← heq, rc7_flip_involutive i ω₁] at this; exact hA1 this
    · simp only [hA1, if_false, hA2, if_false] at heq
      have := congrArg (rc7_flip i) heq
      rwa [rc7_flip_involutive i ω₁, rc7_flip_involutive i ω₂] at this
  · intro ω hω
    rw [mem_filter] at hω; obtain ⟨_, hA⟩ := hω
    by_cases hfA : rc7_flip i ω ∈ A
    · refine ⟨ω, ?_, by simp [hA]⟩
      rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
      rw [rc7_mem_downEvent]
      by_cases hi : ω i = false
      · rw [if_pos hi]; left; exact hA
      · rw [if_neg hi]; exact ⟨hA, hfA⟩
    · by_cases hi : ω i = false
      · refine ⟨ω, ?_, by simp [hA]⟩
        rw [mem_filter]; exact ⟨mem_univ _, by rw [rc7_mem_downEvent, if_pos hi]; left; exact hA⟩
      · have hit : ω i = true := Bool.not_eq_false _ |>.mp hi
        have hfi : rc7_flip i ω i = false := by rw [rc7_flip_self, hit]; rfl
        refine ⟨rc7_flip i ω, ?_, ?_⟩
        · rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
          rw [rc7_mem_downEvent, if_pos hfi]; right; rw [rc7_flip_involutive i ω]; exact hA
        · simp only [hfA, if_false, rc7_flip_involutive i ω]

omit [Fintype α] in
open Classical in


theorem rc7_downEvent_down_in_coord (i : α) (A : Set (ConfigSpace α)) {ω : ConfigSpace α}
    (hω : ω ∈ rc7_downEvent i A) (hi : ω i = true) : rc7_flip i ω ∈ rc7_downEvent i A := by
  rw [rc7_mem_downEvent, if_neg (by rw [hi]; decide)] at hω
  rw [rc7_mem_downEvent, rc7_flip_self, hi, Bool.not_true, if_pos rfl]
  right; rw [rc7_flip_involutive i ω]; exact hω.1

omit [Fintype α] in
open Classical in


theorem rc7_downEvent_idem (i : α) (A : Set (ConfigSpace α)) :
    rc7_downEvent i (rc7_downEvent i A) = rc7_downEvent i A := by
  ext ω
  constructor
  · intro hω
    rw [rc7_mem_downEvent] at hω
    by_cases hi : ω i = false
    · rw [if_pos hi] at hω
      rcases hω with h | h
      · exact h
      · have hd := rc7_downEvent_down_in_coord i A h (by rw [rc7_flip_self, hi]; rfl)
        rwa [rc7_flip_involutive i ω] at hd
    · rw [if_neg hi] at hω; exact hω.1
  · intro hω
    rw [rc7_mem_downEvent]
    by_cases hi : ω i = false
    · rw [if_pos hi]; left; exact hω
    · rw [if_neg hi]
      exact ⟨hω, rc7_downEvent_down_in_coord i A hω (Bool.not_eq_false _ |>.mp hi)⟩

end EventCompression


section Engine

variable {β : Type*} [DecidableEq β]


theorem rc7_compressionEngine (𝒜 ℬ : Finset (Finset β)) :
    ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ)
      ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
      ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
            - dpairsCount 𝒜 ℬ
          = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
            - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
                (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i))
      ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card)
      ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
            ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) :=
  rc6_compressionEngine 𝒜 ℬ

end Engine


section Reflection

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in


theorem rc7_reflectionDeficit (A B : Set (ConfigSpace α)) :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α)
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)))
      ∧ (StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0) :=
  rc5_core_reflectionDeficit A B

end Reflection


theorem rc7_reindexTransfer (hcard : ReimerCardFormAll)
    {β : Type*} [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)) :
    poc_ReimerCardForm A B :=
  rc5_core_reindexTransfer hcard A B


end StatMech.Walls
