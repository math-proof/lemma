/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc14reimerinduct
import Def.StatisticalMechanics.Code.Walls.rc15dimreduce.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc15_bkrground_empty : rc15_BKRground (∅ : Finset α) := by
  intro 𝒜 ℬ _ _
  apply Finset.card_le_card
  intro S hS
  rw [rc14_mem_boxE] at hS
  obtain ⟨hSE, K, L, _, hKS, hLS, hK, hL⟩ := hS
  have hS0 : S = ∅ := Finset.subset_empty.mp hSE
  subst hS0
  have hK0 : K = ∅ := Finset.subset_empty.mp hKS
  have hL0 : L = ∅ := Finset.subset_empty.mp hLS
  subst hK0; subst hL0
  rw [rc14_mem_reflE]
  refine ⟨Finset.Subset.refl _, hK, ?_⟩
  simpa using hL


open Classical in


theorem rc15_bkrground_step {E : Finset α} (hUnion : rc15_SliceUnionBound (α := α)) {a : α}
    (haE : a ∈ E) (hIH : rc15_BKRground (E.erase a)) : rc15_BKRground E := by
  intro 𝒜 ℬ h𝒜 hℬ
  set F := E.erase a with hF
  set 𝒜₀ := 𝒜.nonMemberSubfamily a
  set 𝒜₁ := 𝒜.memberSubfamily a
  set ℬ₀ := ℬ.nonMemberSubfamily a
  set ℬ₁ := ℬ.memberSubfamily a
  rw [rc15_card_boxE_slice h𝒜 a haE, rc15_card_reflE_slice E 𝒜 ℬ a haE]
  
  have hIH00 : #(rc14_boxE F 𝒜₀ ℬ₀) ≤ #(rc14_reflE F 𝒜₀ ℬ₀) :=
    hIH 𝒜₀ ℬ₀ (rc15_upperOn_nonMember h𝒜 a) (rc15_upperOn_nonMember hℬ a)
  
  have hmono : #(rc14_reflE F 𝒜₀ ℬ₀) ≤ #(rc14_reflE F 𝒜₁ ℬ₀) :=
    rc15_card_reflE_nonMem_le_mem h𝒜 a haE
  
  have hres : #(rc14_boxE F 𝒜₁ ℬ₀ ∪ rc14_boxE F 𝒜₀ ℬ₁) ≤ #(rc14_reflE F 𝒜₀ ℬ₁) :=
    hUnion E 𝒜 ℬ a haE h𝒜 hℬ
  
  calc #(rc14_boxE F 𝒜₀ ℬ₀) + #(rc14_boxE F 𝒜₁ ℬ₀ ∪ rc14_boxE F 𝒜₀ ℬ₁)
      ≤ #(rc14_reflE F 𝒜₁ ℬ₀) + #(rc14_reflE F 𝒜₀ ℬ₁) := by
        exact Nat.add_le_add (le_trans hIH00 hmono) hres
    _ = #(rc14_reflE F 𝒜₀ ℬ₁) + #(rc14_reflE F 𝒜₁ ℬ₀) := Nat.add_comm _ _

open Classical in


theorem rc15_bkrground_of_sliceUnion (hUnion : rc15_SliceUnionBound (α := α)) :
    ∀ E : Finset α, rc15_BKRground E := by
  intro E
  induction E using Finset.strongInduction with
  | _ E ih =>
    rcases E.eq_empty_or_nonempty with rfl | ⟨a, haE⟩
    · exact rc15_bkrground_empty
    · exact rc15_bkrground_step hUnion haE (ih (E.erase a) (Finset.erase_ssubset haE))


open Classical in

theorem rc15_boxE_univ (𝒜 ℬ : Finset (Finset α)) :
    rc14_boxE (univ : Finset α) 𝒜 ℬ = rc10_boxSupp 𝒜 ℬ := by
  ext S
  rw [rc14_mem_boxE, rc11_mem_boxSupp]
  simp only [Finset.subset_univ, true_and]

open Classical in

theorem rc15_reflE_univ (𝒜 ℬ : Finset (Finset α)) :
    rc14_reflE (univ : Finset α) 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
  ext S
  rw [rc14_mem_reflE, rc11_mem_reflInter]
  simp only [Finset.subset_univ, true_and, Finset.compl_eq_univ_sdiff]

open Classical in


theorem rc15_bkrSetFamily_of_bkrground (h : ∀ (β : Type) [Fintype β] [DecidableEq β],
    rc15_BKRground (univ : Finset β)) : rc10_BKRSetFamily := by
  intro n 𝒜 ℬ h𝒜 hℬ
  have := h (Fin n) 𝒜 ℬ ((rc15_upperOn_univ_iff 𝒜).mpr h𝒜) ((rc15_upperOn_univ_iff ℬ).mpr hℬ)
  rwa [rc15_boxE_univ, rc15_reflE_univ] at this


open Classical in


theorem rc15_bkrSetFamily_of_sliceUnion
    (hUnion : ∀ (β : Type) [Fintype β] [DecidableEq β], rc15_SliceUnionBound (α := β)) :
    rc10_BKRSetFamily :=
  rc15_bkrSetFamily_of_bkrground
    (fun β _ _ => rc15_bkrground_of_sliceUnion (hUnion β) univ)


open Classical in


theorem rc15_sliceUnion_empty_left {E : Finset α} (ℬ : Finset (Finset α)) (a : α) :
    #(rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).memberSubfamily a) (ℬ.nonMemberSubfamily a)
        ∪ rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).nonMemberSubfamily a) (ℬ.memberSubfamily a))
      ≤ #(rc14_reflE (E.erase a) ((∅ : Finset (Finset α)).nonMemberSubfamily a)
          (ℬ.memberSubfamily a)) := by
  have hbox : ∀ ℬ' : Finset (Finset α),
      rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).memberSubfamily a) ℬ' = ∅ := by
    intro ℬ'
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    rw [rc14_mem_boxE] at hS
    obtain ⟨_, K, _, _, _, _, hK, _⟩ := hS
    rw [mem_memberSubfamily] at hK
    exact absurd hK.1 (by simp)
  have hbox2 : ∀ ℬ' : Finset (Finset α),
      rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).nonMemberSubfamily a) ℬ' = ∅ := by
    intro ℬ'
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    rw [rc14_mem_boxE] at hS
    obtain ⟨_, K, _, _, _, _, hK, _⟩ := hS
    rw [mem_nonMemberSubfamily] at hK
    exact absurd hK.1 (by simp)
  rw [hbox, hbox2, Finset.union_empty]
  simp

end StatMech.Walls
