/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc28cylrec.Part4
import Def.StatisticalMechanics.Code.Walls.rc29reconcile.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc29_flipAComp_eq (n : ℕ) (a : Fin n) (ℬ : Finset (Finset (Fin n))) :
    rc29_flipAComp n a ℬ = rc29_flipA a ℬ := rfl


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc29_box_flip_strictDecrease :
    #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}})
        ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}}))
      > #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}})
          (rc29_flipA 0 ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))))) := by
  rw [← rc29_flipAComp_eq, ← rc28_famCylBoxEComp_eq, ← rc28_famCylBoxEComp_eq]
  decide


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc29_flipCandidate_witness :
    #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}, {2}, {0, 1}})
        ({∅, {0}, {1}, {0, 1}, {0, 2}}))
      ≤ #(rc14_reflE (univ : Finset (Fin 3)) ({∅, {0}, {1}, {2}, {0, 1}})
          (rc29_flipA 0 ({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))))) := by
  rw [← rc29_flipAComp_eq, ← rc28_famCylBoxEComp_eq, ← rc28_reflEComp_eq]
  decide


open Classical in


theorem rc29_famCylBox_le_reflInter_flip
    (hwall : ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)),
      #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ))
    (𝒜 ℬ : Finset (Finset α)) (a : α) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 (rc29_flipA a ℬ)) := by
  have h := rc29_flipCandidate_of_wall hwall (E := (univ : Finset α)) 𝒜 ℬ (Finset.mem_univ a)
  rwa [rc28_famCylBoxE_univ, rc15_reflE_univ] at h


theorem rc29_toggle_compl (a : α) (S : Finset α) :
    (if a ∈ S then S.erase a else insert a S)ᶜ
      = (if a ∈ Sᶜ then Sᶜ.erase a else insert a Sᶜ) := by
  by_cases ha : a ∈ S
  · have hac : a ∉ Sᶜ := by rw [Finset.mem_compl]; exact fun h => h ha
    rw [if_pos ha, if_neg hac, Finset.compl_erase]
  · have hac : a ∈ Sᶜ := by rw [Finset.mem_compl]; exact ha
    rw [if_neg ha, if_pos hac, Finset.compl_insert]

open Classical in


theorem rc29_reflInter_doubleFlip (a : α) (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter (rc29_flipA a 𝒜) (rc29_flipA a ℬ)) = #(rc10_reflInter 𝒜 ℬ) := by
  apply Finset.card_bij (fun S _ => (if a ∈ S then S.erase a else insert a S))
  · intro S hS
    rw [rc20_mem_reflInter, rc29_mem_flipA, rc29_mem_flipA] at hS
    rw [rc20_mem_reflInter, rc29_toggle_compl]
    exact hS
  · intro S hS S' hS' h
    have := congrArg (fun T => if a ∈ T then T.erase a else insert a T) h
    simpa only [rc29_toggle_involutive] using this
  · intro T hT
    refine ⟨if a ∈ T then T.erase a else insert a T, ?_, rc29_toggle_involutive a T⟩
    rw [rc20_mem_reflInter] at hT
    rw [rc20_mem_reflInter, rc29_mem_flipA, rc29_mem_flipA, rc29_toggle_involutive,
      rc29_toggle_compl, rc29_toggle_involutive]
    exact hT

end StatMech.Walls
