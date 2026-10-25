/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc28cylrec.Part4
import Def.StatisticalMechanics.Code.Walls.rc29reconcile
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] in

theorem rc29_toggle_involutive (a : α) (S : Finset α) :
    (if a ∈ (if a ∈ S then S.erase a else insert a S) then
        (if a ∈ S then S.erase a else insert a S).erase a
      else insert a (if a ∈ S then S.erase a else insert a S)) = S := by
  by_cases ha : a ∈ S
  · simp only [ha, if_true]
    have : a ∉ S.erase a := Finset.notMem_erase a S
    simp only [this, if_false, Finset.insert_erase ha]
  · simp only [ha, if_false]
    have : a ∈ insert a S := Finset.mem_insert_self a S
    simp only [this, if_true, Finset.erase_insert ha]

omit [Fintype α] in


theorem rc29_mem_flipA (a : α) (ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc29_flipA a ℬ ↔ (if a ∈ S then S.erase a else insert a S) ∈ ℬ := by
  rw [rc29_flipA, Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    rwa [rc29_toggle_involutive a T]
  · intro h
    exact ⟨_, h, rc29_toggle_involutive a S⟩

omit [Fintype α] in


theorem rc29_flipA_nonMemberSubfamily (a : α) (ℬ : Finset (Finset α)) :
    (rc29_flipA a ℬ).nonMemberSubfamily a = ℬ.memberSubfamily a := by
  ext S
  rw [Finset.mem_nonMemberSubfamily, rc29_mem_flipA, Finset.mem_memberSubfamily]
  constructor
  · rintro ⟨hmem, haS⟩
    rw [if_neg haS] at hmem
    exact ⟨hmem, haS⟩
  · rintro ⟨hmem, haS⟩
    rw [if_neg haS]
    exact ⟨hmem, haS⟩

omit [Fintype α] in


theorem rc29_flipA_memberSubfamily (a : α) (ℬ : Finset (Finset α)) :
    (rc29_flipA a ℬ).memberSubfamily a = ℬ.nonMemberSubfamily a := by
  ext S
  rw [Finset.mem_memberSubfamily, rc29_mem_flipA, Finset.mem_nonMemberSubfamily]
  constructor
  · rintro ⟨hmem, haS⟩
    have hain : a ∈ insert a S := Finset.mem_insert_self a S
    rw [if_pos hain, Finset.erase_insert haS] at hmem
    exact ⟨hmem, haS⟩
  · rintro ⟨hmem, haS⟩
    have hain : a ∈ insert a S := Finset.mem_insert_self a S
    rw [if_pos hain, Finset.erase_insert haS]
    exact ⟨hmem, haS⟩


open Classical in


theorem rc29_flippedBox_crossRecursion {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α}
    (haE : a ∈ E) :
    #(rc28_famCylBoxE E 𝒜 (rc29_flipA a ℬ))
      ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
  have h := rc28_sameSideRecursion 𝒜 (rc29_flipA a ℬ) haE
  rwa [rc29_flipA_nonMemberSubfamily, rc29_flipA_memberSubfamily] at h


open Classical in


theorem rc29_flippedReflE_sameSideRecursion {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α}
    (haE : a ∈ E) :
    #(rc14_reflE E 𝒜 (rc29_flipA a ℬ))
      = #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
  have h := rc27_reflInterRecursion E 𝒜 (rc29_flipA a ℬ) a haE
  rwa [rc29_flipA_memberSubfamily, rc29_flipA_nonMemberSubfamily] at h


open Classical in


theorem rc29_box_le_flippedReflE {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α} (haE : a ∈ E)
    (hwnn : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)))
    (hwmm : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))) :
    #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 (rc29_flipA a ℬ)) := by
  have hrec := rc28_sameSideRecursion 𝒜 ℬ haE
  have hflip := rc29_flippedReflE_sameSideRecursion 𝒜 ℬ haE
  omega


open Classical in


theorem rc29_flipCandidate_of_wall
    (hwall : ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)),
      #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ))
    {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α} (haE : a ∈ E) :
    #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 (rc29_flipA a ℬ)) :=
  rc29_box_le_flippedReflE 𝒜 ℬ haE
    (hwall (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
    (hwall (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))


end StatMech.Walls
