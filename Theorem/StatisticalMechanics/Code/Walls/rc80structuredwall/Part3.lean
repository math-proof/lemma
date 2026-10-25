/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part4
import Def.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


variable {κ : Type*} [Fintype κ] [DecidableEq κ]


@[simp] theorem rc80_mem_projL (K : Finset (ι ⊕ κ)) (i : ι) :
    i ∈ rc80_projL K ↔ Sum.inl i ∈ K := by simp [rc80_projL]

@[simp] theorem rc80_mem_projR (K : Finset (ι ⊕ κ)) (j : κ) :
    j ∈ rc80_projR K ↔ Sum.inr j ∈ K := by simp [rc80_projR]


theorem rc80_occ_prodFam_iff (A₁ : Finset (ConfigSpace ι)) (A₂ : Finset (ConfigSpace κ))
    (K : Finset (ι ⊕ κ)) (w : ConfigSpace (ι ⊕ κ)) :
    rc80_occ (rc80_prodFam A₁ A₂) K w = true
      ↔ rc80_occ A₁ (rc80_projL K) (rc80_restL w) = true
        ∧ rc80_occ A₂ (rc80_projR K) (rc80_restR w) = true := by
  simp only [rc80_occ, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · 
      intro u' hu'
      have := h (Sum.elim u' (rc80_restR w)) ?_
      · rw [rc80_mem_prodFam] at this
        have hL : rc80_restL (Sum.elim u' (rc80_restR w)) = u' := by funext i; rfl
        rw [hL] at this; exact this.1
      · intro e he
        cases e with
        | inl i =>
            show u' i = rc80_restL w i
            exact hu' i (by rw [rc80_mem_projL]; exact he)
        | inr j => rfl
    · intro v' hv'
      have := h (Sum.elim (rc80_restL w) v') ?_
      · rw [rc80_mem_prodFam] at this
        have hR : rc80_restR (Sum.elim (rc80_restL w) v') = v' := by funext j; rfl
        rw [hR] at this; exact this.2
      · intro e he
        cases e with
        | inl i => rfl
        | inr j =>
            show v' j = rc80_restR w j
            exact hv' j (by rw [rc80_mem_projR]; exact he)
  · rintro ⟨h1, h2⟩ w' hw'
    rw [rc80_mem_prodFam]
    refine ⟨h1 (rc80_restL w') ?_, h2 (rc80_restR w') ?_⟩
    · intro i hi; exact hw' (Sum.inl i) (by rwa [rc80_mem_projL] at hi)
    · intro j hj; exact hw' (Sum.inr j) (by rwa [rc80_mem_projR] at hj)


theorem rc80_disjOcc_prod_card
    (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)) :
    (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
      = (rc80_disjOccG A₁ B₁).card * (rc80_disjOccG A₂ B₂).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun w _ => (rc80_restL w, rc80_restR w))
  · 
    intro w hw
    simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨K, L, hKL, hK, hL⟩ := hw
    rw [rc80_occ_prodFam_iff] at hK hL
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨rc80_projL K, rc80_projL L, ?_, hK.1, hL.1⟩
      rw [Finset.disjoint_left]
      intro i hiK hiL
      rw [rc80_mem_projL] at hiK hiL
      exact (Finset.disjoint_left.mp hKL hiK) hiL
    · simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨rc80_projR K, rc80_projR L, ?_, hK.2, hL.2⟩
      rw [Finset.disjoint_left]
      intro j hjK hjL
      rw [rc80_mem_projR] at hjK hjL
      exact (Finset.disjoint_left.mp hKL hjK) hjL
  · 
    intro w hw v hv h
    rw [Prod.mk.injEq] at h
    obtain ⟨hL, hR⟩ := h
    funext x
    cases x with
    | inl i => exact congrFun hL i
    | inr j => exact congrFun hR j
  · 
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hqA, hqB⟩ := hq
    simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at hqA hqB
    obtain ⟨K₁, L₁, hKL₁, hK₁, hL₁⟩ := hqA
    obtain ⟨K₂, L₂, hKL₂, hK₂, hL₂⟩ := hqB
    refine ⟨Sum.elim q.1 q.2, ?_, ?_⟩
    · simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨K₁.image Sum.inl ∪ K₂.image Sum.inr, L₁.image Sum.inl ∪ L₂.image Sum.inr, ?_, ?_, ?_⟩
      · 
        rw [Finset.disjoint_left]
        intro e heK heL
        simp only [Finset.mem_union, Finset.mem_image] at heK heL
        rcases heK with ⟨i, hiK, rfl⟩ | ⟨j, hjK, rfl⟩
        · rcases heL with ⟨i', hiL, hii⟩ | ⟨j', hjL, hij⟩
          · rw [Sum.inl.injEq] at hii; subst hii; exact (Finset.disjoint_left.mp hKL₁ hiK) hiL
          · exact absurd hij (by simp)
        · rcases heL with ⟨i', hiL, hij⟩ | ⟨j', hjL, hjj⟩
          · exact absurd hij (by simp)
          · rw [Sum.inr.injEq] at hjj; subst hjj; exact (Finset.disjoint_left.mp hKL₂ hjK) hjL
      · 
        rw [rc80_occ_prodFam_iff]
        constructor
        · have hpL : rc80_projL (K₁.image Sum.inl ∪ K₂.image Sum.inr) = K₁ := by
            ext i; simp [rc80_projL]
          have hwL : rc80_restL (Sum.elim q.1 q.2) = q.1 := by funext i; rfl
          rw [hpL, hwL]; exact hK₁
        · have hpR : rc80_projR (K₁.image Sum.inl ∪ K₂.image Sum.inr) = K₂ := by
            ext j; simp [rc80_projR]
          have hwR : rc80_restR (Sum.elim q.1 q.2) = q.2 := by funext j; rfl
          rw [hpR, hwR]; exact hK₂
      · 
        rw [rc80_occ_prodFam_iff]
        constructor
        · have hpL : rc80_projL (L₁.image Sum.inl ∪ L₂.image Sum.inr) = L₁ := by
            ext i; simp [rc80_projL]
          have hwL : rc80_restL (Sum.elim q.1 q.2) = q.1 := by funext i; rfl
          rw [hpL, hwL]; exact hL₁
        · have hpR : rc80_projR (L₁.image Sum.inl ∪ L₂.image Sum.inr) = L₂ := by
            ext j; simp [rc80_projR]
          have hwR : rc80_restR (Sum.elim q.1 q.2) = q.2 := by funext j; rfl
          rw [hpR, hwR]; exact hL₂
    · rw [Prod.mk.injEq]; exact ⟨by funext i; rfl, by funext j; rfl⟩


theorem rc80_wall_product
    (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ))
    (h1 : (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card)
    (h2 : (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card) :
    (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
      ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card := by
  rw [rc80_reflInter_prod_card, rc80_disjOcc_prod_card]
  exact Nat.mul_le_mul h1 h2


theorem rc80_monoWitness_upper : rc80_IsUpper ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) := by
  intro a ha i
  rw [Finset.mem_singleton] at ha ⊢
  subst ha; funext j; simp [Function.update]

theorem rc80_monoWitness_lower : rc80_IsLower ({(fun _ => false)} : Finset (ConfigSpace (Fin 2))) := by
  intro a ha i
  rw [Finset.mem_singleton] at ha ⊢
  subst ha; funext j; simp [Function.update]


theorem rc80_monoWitness_reduces :
    rc80_disjOccG ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) {(fun _ => false)}
      = ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) ∩ {(fun _ => false)} :=
  rc80_disjOcc_eq_inter_of_upper_lower rc80_monoWitness_upper rc80_monoWitness_lower


theorem rc80_prodWitness_reflInter :
    (rc80_reflInterG
        (rc80_prodFam ({(fun _ => true)} : Finset (ConfigSpace (Fin 1)))
          ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))))
        (rc80_prodFam ({(fun _ => false)} : Finset (ConfigSpace (Fin 1)))
          ({(fun _ => false)} : Finset (ConfigSpace (Fin 1))))).card
      = (rc80_reflInterG ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))) {(fun _ => false)}).card
        * (rc80_reflInterG ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))) {(fun _ => false)}).card :=
  rc80_reflInter_prod_card _ _ _ _

open Classical in


theorem rc80_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc79_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in 


theorem rc80_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧
    
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          = (rc80_disjOccG A₁ B₁).card * (rc80_disjOccG A₂ B₂).card) ∧
    
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          = (rc80_reflInterG A₁ B₁).card * (rc80_reflInterG A₂ B₂).card) ∧
    
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card →
        (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card →
        (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _ _ hA hB => rc80_disjOcc_eq_inter_of_upper_lower hA hB,
   fun A₁ B₁ A₂ B₂ => rc80_disjOcc_prod_card A₁ B₁ A₂ B₂,
   fun A₁ B₁ A₂ B₂ => rc80_reflInter_prod_card A₁ B₁ A₂ B₂,
   fun A₁ B₁ A₂ B₂ => rc80_wall_product A₁ B₁ A₂ B₂,
   rc79_top_wall_fin2,
   rc80_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
