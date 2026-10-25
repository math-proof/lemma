/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc27recursion.Part2
import Def.StatisticalMechanics.Code.Walls.rc28cylrec.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc28_crossRecursion_false :
    ¬ (#(rc28_famCylBoxE (univ : Finset (Fin 3))
          ({∅, {0}, {1}, {2}, {0, 1}}) ({∅, {0}, {1}, {0, 1}, {0, 2}}))
        ≤ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
              (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
              (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0))
          + #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
              (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).memberSubfamily 0)
              (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))) := by
  rw [← rc28_famCylBoxEComp_eq, ← rc28_famCylBoxEComp_eq, ← rc28_famCylBoxEComp_eq]
  decide


open Classical in


theorem rc28_target_empty (𝒜 ℬ : Finset (Finset α)) :
    #(rc28_famCylBoxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ) := by
  apply Finset.card_le_card
  intro S hS
  rw [rc28_mem_famCylBoxE] at hS
  obtain ⟨hSE, K, L, _, hKA, hLB⟩ := hS
  have hS0 : S = ∅ := Finset.subset_empty.mp hSE
  subst hS0
  rw [rc14_mem_reflE]
  refine ⟨Finset.Subset.refl _, ?_, ?_⟩
  · exact hKA ∅ (Finset.Subset.refl _) rfl
  · simpa using hLB ∅ (Finset.Subset.refl _) rfl

open Classical in


theorem rc28_target_of_crossRecursion (h : rc28_CrossRecursion (α := α)) :
    ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α),
      #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ) := by
  intro E
  induction E using Finset.strongInduction with
  | _ E ih =>
    intro 𝒜 ℬ
    rcases E.eq_empty_or_nonempty with rfl | ⟨a, haE⟩
    · exact rc28_target_empty 𝒜 ℬ
    · have hIHnm : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
          ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) :=
        ih (E.erase a) (Finset.erase_ssubset haE) _ _
      have hIHmn : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))
          ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) :=
        ih (E.erase a) (Finset.erase_ssubset haE) _ _
      have hcross := h E 𝒜 ℬ a haE
      have hrefl := rc27_reflInterRecursion E 𝒜 ℬ a haE
      omega


open Classical in


theorem rc28_box_le_sameSide_reflSum {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α} (haE : a ∈ E)
    (hIHnn : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)))
    (hIHmm : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))) :
    #(rc28_famCylBoxE E 𝒜 ℬ)
      ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
  have hrec := rc28_sameSideRecursion 𝒜 ℬ haE
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc28_sameSide_reflSum_overshoots :
    #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}})) <
      #(rc28_reflEComp 3 ((univ : Finset (Fin 3)).erase 0)
          (({∅} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
          (({{1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))
        + #(rc28_reflEComp 3 ((univ : Finset (Fin 3)).erase 0)
            (({∅} : Finset (Finset (Fin 3))).memberSubfamily 0)
            (({{1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) := by
  rw [← rc28_reflEComp_eq]
  decide


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc28_sameSideRecursion_witness :
    #(rc28_famCylBoxE (univ : Finset (Fin 3))
        ({∅, {0}, {0, 1}, {1}}) ({∅, {0}, {0, 2}, {2}})) = 2
      ∧ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
            (({∅, {0}, {0, 1}, {1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
            (({∅, {0}, {0, 2}, {2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)) = 1
      ∧ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
            (({∅, {0}, {0, 1}, {1}} : Finset (Finset (Fin 3))).memberSubfamily 0)
            (({∅, {0}, {0, 2}, {2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [← rc28_famCylBoxEComp_eq]; decide)


open Classical in


theorem rc28_famCylBoxResidue_of_crossRecursion
    (h : ∀ {β : Type} [Fintype β] [DecidableEq β], rc28_CrossRecursion (α := β)) :
    rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  have hkey := rc28_target_of_crossRecursion (h (β := Fin n)) univ 𝒜 ℬ
  rwa [rc28_famCylBoxE_univ, rc15_reflE_univ] at hkey


open Classical in


theorem rc28_reimer_cylrec :
    (∀ (𝒜 ℬ : Finset (Finset α)), rc28_famCylBoxE univ 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ)
      ∧ (∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E →
          #(rc28_famCylBoxE E 𝒜 ℬ)
            ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
              + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)))
      ∧ (¬ (#(rc28_famCylBoxE (univ : Finset (Fin 3))
              ({∅, {0}, {1}, {2}, {0, 1}}) ({∅, {0}, {1}, {0, 1}, {0, 2}}))
            ≤ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
                  (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
                  (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0))
              + #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
                  (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).memberSubfamily 0)
                  (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))))
      ∧ (rc28_CrossRecursion (α := α) →
          ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α),
            #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)) :=
  ⟨rc28_famCylBoxE_univ,
    fun _ 𝒜 ℬ _ haE => rc28_sameSideRecursion 𝒜 ℬ haE,
    rc28_crossRecursion_false,
    rc28_target_of_crossRecursion⟩

end StatMech.Walls
