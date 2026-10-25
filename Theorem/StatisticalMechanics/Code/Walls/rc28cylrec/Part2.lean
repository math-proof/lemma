/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc27recursion.Part2
import Def.StatisticalMechanics.Code.Walls.rc28cylrec.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc28_traceClassE_subset_iff (n : ℕ) (E K S : Finset (Fin n)) (𝒜 : Finset (Finset (Fin n))) :
    rc28_traceClassE n E K S ⊆ 𝒜 ↔ ∀ T : Finset (Fin n), T ⊆ E → T ∩ K = S ∩ K → T ∈ 𝒜 := by
  rw [rc28_traceClassE]
  constructor
  · intro h T hTE hT
    exact h (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTE, hT⟩)
  · intro h T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    exact h T hT.1 hT.2

omit [Fintype α] in


theorem rc28_traceCond_inter_ground {E K S T : Finset α} (hSE : S ⊆ E) (hTE : T ⊆ E) :
    T ∩ (K ∩ E) = S ∩ (K ∩ E) ↔ T ∩ K = S ∩ K := by
  constructor
  · intro h
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hxT, hxK⟩
      have hxE : x ∈ E := hTE hxT
      have : x ∈ T ∩ (K ∩ E) := Finset.mem_inter.mpr ⟨hxT, Finset.mem_inter.mpr ⟨hxK, hxE⟩⟩
      rw [h] at this
      exact ⟨(Finset.mem_inter.mp this).1, hxK⟩
    · rintro ⟨hxS, hxK⟩
      have hxE : x ∈ E := hSE hxS
      have : x ∈ S ∩ (K ∩ E) := Finset.mem_inter.mpr ⟨hxS, Finset.mem_inter.mpr ⟨hxK, hxE⟩⟩
      rw [← h] at this
      exact ⟨(Finset.mem_inter.mp this).1, hxK⟩
  · intro h
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hxT, hxK, hxE⟩
      have : x ∈ T ∩ K := Finset.mem_inter.mpr ⟨hxT, hxK⟩
      rw [h] at this
      exact ⟨(Finset.mem_inter.mp this).1, hxK, hxE⟩
    · rintro ⟨hxS, hxK, hxE⟩
      have : x ∈ S ∩ K := Finset.mem_inter.mpr ⟨hxS, hxK⟩
      rw [← h] at this
      exact ⟨(Finset.mem_inter.mp this).1, hxK, hxE⟩

open Classical in

theorem rc28_famCylBoxEComp_eq (n : ℕ) (E : Finset (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc28_famCylBoxEComp n E 𝒜 ℬ = rc28_famCylBoxE E 𝒜 ℬ := by
  ext S
  rw [rc28_famCylBoxEComp, rc28_famCylBoxE, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq]
  refine and_congr_right (fun hSp => ?_)
  rw [Finset.mem_powerset] at hSp
  constructor
  · rintro ⟨K, _, L, _, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, (rc28_traceClassE_subset_iff n E K S 𝒜).mp hKA,
      (rc28_traceClassE_subset_iff n E L S ℬ).mp hLB⟩
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    refine ⟨K ∩ E, Finset.mem_powerset.mpr Finset.inter_subset_right, L ∩ E,
      Finset.mem_powerset.mpr Finset.inter_subset_right, ?_, ?_, ?_⟩
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hKL)
    · rw [rc28_traceClassE_subset_iff]
      intro T hTE hT
      exact hKA T hTE ((rc28_traceCond_inter_ground hSp hTE).mp hT)
    · rw [rc28_traceClassE_subset_iff]
      intro T hTE hT
      exact hLB T hTE ((rc28_traceCond_inter_ground hSp hTE).mp hT)


open Classical in


theorem rc28_famCylBoxE_univ (𝒜 ℬ : Finset (Finset α)) :
    rc28_famCylBoxE univ 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
  ext S
  rw [rc28_mem_famCylBoxE, rc21_mem_famCylBox]
  constructor
  · rintro ⟨_, K, L, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, fun T hT => hKA T (Finset.subset_univ T) hT,
      fun T hT => hLB T (Finset.subset_univ T) hT⟩
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨Finset.subset_univ S, K, L, hKL, fun T _ hT => hKA T hT, fun T _ hT => hLB T hT⟩


open Classical in


theorem rc28_notMem_fiber_subset {E : Finset α} {𝒜 ℬ : Finset (Finset α)} {a : α}
    {S : Finset α} (hS : S ∈ rc28_famCylBoxE E 𝒜 ℬ) (haS : a ∉ S) :
    S ∈ rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a) := by
  rw [rc28_mem_famCylBoxE] at hS ⊢
  obtain ⟨hSE, K, L, hKL, hKA, hLB⟩ := hS
  have hSF : S ⊆ E.erase a := fun x hx => Finset.mem_erase.mpr ⟨fun h => haS (h ▸ hx), hSE hx⟩
  refine ⟨hSF, K, L, hKL, ?_, ?_⟩
  · intro T hTF hTK
    have hTE : T ⊆ E := hTF.trans (Finset.erase_subset a E)
    have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTF h)).1 rfl
    exact Finset.mem_nonMemberSubfamily.mpr ⟨hKA T hTE hTK, haT⟩
  · intro T hTF hTL
    have hTE : T ⊆ E := hTF.trans (Finset.erase_subset a E)
    have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTF h)).1 rfl
    exact Finset.mem_nonMemberSubfamily.mpr ⟨hLB T hTE hTL, haT⟩

omit [Fintype α] in


theorem rc28_insert_trace_eq {K S T : Finset α} {a : α} (haS : a ∈ S) (haT : a ∉ T)
    (h : T ∩ K.erase a = (S.erase a) ∩ K.erase a) :
    (insert a T) ∩ K = S ∩ K := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  by_cases hxa : x = a
  · subst hxa
    simp only [haS, true_and]
    tauto
  · constructor
    · rintro ⟨hxT | hxT, hxK⟩
      · exact absurd hxT hxa
      · have : x ∈ T ∩ K.erase a :=
          Finset.mem_inter.mpr ⟨hxT, Finset.mem_erase.mpr ⟨hxa, hxK⟩⟩
        rw [h] at this
        exact ⟨(Finset.mem_erase.mp (Finset.mem_inter.mp this).1).2, hxK⟩
    · rintro ⟨hxS, hxK⟩
      have : x ∈ (S.erase a) ∩ K.erase a :=
        Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxa, hxS⟩, Finset.mem_erase.mpr ⟨hxa, hxK⟩⟩
      rw [← h] at this
      exact ⟨Or.inr (Finset.mem_inter.mp this).1, hxK⟩

open Classical in


theorem rc28_mem_fiber_subset {E : Finset α} {𝒜 ℬ : Finset (Finset α)} {a : α}
    {S : Finset α} (hS : S ∈ rc28_famCylBoxE E 𝒜 ℬ) (haS : a ∈ S) :
    S.erase a ∈ rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a) := by
  rw [rc28_mem_famCylBoxE] at hS ⊢
  obtain ⟨hSE, K, L, hKL, hKA, hLB⟩ := hS
  have hSF : S.erase a ⊆ E.erase a := Finset.erase_subset_erase a hSE
  refine ⟨hSF, K.erase a, L.erase a, ?_, ?_, ?_⟩
  · exact Finset.disjoint_of_subset_left (Finset.erase_subset a K)
      (Finset.disjoint_of_subset_right (Finset.erase_subset a L) hKL)
  · intro T hTF hTK
    have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTF h)).1 rfl
    have hTE : insert a T ⊆ E := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact hSE haS
      · exact (Finset.erase_subset a E) (hTF hxT)
    have htrace : (insert a T) ∩ K = S ∩ K := rc28_insert_trace_eq haS haT hTK
    exact Finset.mem_memberSubfamily.mpr ⟨hKA (insert a T) hTE htrace, haT⟩
  · intro T hTF hTL
    have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTF h)).1 rfl
    have hTE : insert a T ⊆ E := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact hSE haS
      · exact (Finset.erase_subset a E) (hTF hxT)
    have htrace : (insert a T) ∩ L = S ∩ L := rc28_insert_trace_eq haS haT hTL
    exact Finset.mem_memberSubfamily.mpr ⟨hLB (insert a T) hTE htrace, haT⟩


set_option linter.unusedVariables false in
open Classical in


theorem rc28_sameSideRecursion {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α} (haE : a ∈ E) :
    #(rc28_famCylBoxE E 𝒜 ℬ)
      ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := rc28_famCylBoxE E 𝒜 ℬ) (p := fun S => a ∈ S)]
  have hle_in :
      #((rc28_famCylBoxE E 𝒜 ℬ).filter (fun S => a ∈ S))
        ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
    apply Finset.card_le_card_of_injOn (fun S => S.erase a)
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_filter] at hS
      exact Finset.mem_coe.mpr (rc28_mem_fiber_subset hS.1 hS.2)
    · intro S hS S' hS' h
      rw [Finset.mem_coe, Finset.mem_filter] at hS hS'
      have := congrArg (insert a) h
      rwa [Finset.insert_erase hS.2, Finset.insert_erase hS'.2] at this
  have hle_notin :
      #((rc28_famCylBoxE E 𝒜 ℬ).filter (fun S => ¬ a ∈ S))
        ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
    apply Finset.card_le_card
    intro S hS
    rw [Finset.mem_filter] at hS
    exact rc28_notMem_fiber_subset hS.1 hS.2
  omega


end StatMech.Walls
