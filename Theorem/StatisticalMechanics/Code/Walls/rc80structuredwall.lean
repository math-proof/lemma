/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part4
import Def.StatisticalMechanics.Code.Walls.rc80structuredwall
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc80_minext_agree (K : Finset ι) (w : ConfigSpace ι) {e : ι} (he : e ∈ K) :
    rc80_minext K w e = w e := by simp [rc80_minext, he]


theorem rc80_maxext_agree (L : Finset ι) (w : ConfigSpace ι) {e : ι} (he : e ∈ L) :
    rc80_maxext L w e = w e := by simp [rc80_maxext, he]


theorem rc80_minext_le (K : Finset ι) (w : ConfigSpace ι) (i : ι) :
    rc80_minext K w i = true → w i = true := by
  simp only [rc80_minext]
  split <;> simp_all


theorem rc80_le_maxext (L : Finset ι) (w : ConfigSpace ι) (i : ι) :
    w i = true → rc80_maxext L w i = true := by
  simp only [rc80_maxext]
  split <;> simp_all


theorem rc80_upper_mono {A : Finset (ConfigSpace ι)} (hA : rc80_IsUpper A)
    {a b : ConfigSpace ι} (hab : ∀ i, a i = true → b i = true) (ha : a ∈ A) : b ∈ A := by
  
  classical
  set D : Finset ι := Finset.univ.filter (fun i => a i = false ∧ b i = true) with hD
  
  suffices H : ∀ (S : Finset ι) (c : ConfigSpace ι), c ∈ A →
      (∀ i, i ∉ S → c i = b i) → (∀ i ∈ S, c i = false) → b ∈ A by
    
    refine H D a ha ?_ ?_
    · intro i hi
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
      
      cases hai : a i
      · 
        have hbi : b i ≠ true := hi hai
        have : b i = false := Bool.eq_false_iff.mpr hbi
        rw [this]
      · 
        rw [hab i hai]
    · intro i hi
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi.1
  intro S
  induction S using Finset.induction with
  | empty => intro c hc hoff _
             have : c = b := funext (fun i => hoff i (Finset.notMem_empty i)); rwa [this] at hc
  | @insert j S hj ih =>
      intro c hc hoff hon
      
      
      
      have hcj : c j = false := hon j (Finset.mem_insert_self j S)
      
      
      by_cases hbj : b j = true
      · set c' := Function.update c j true with hc'
        have hc'A : c' ∈ A := hA c hc j
        refine ih c' hc'A ?_ ?_
        · intro i hi
          rw [hc']
          by_cases hij : i = j
          · subst hij; rw [Function.update_self]; exact hbj.symm
          · rw [Function.update_of_ne hij]
            exact hoff i (fun hmem => (Finset.mem_insert.mp hmem).elim (fun h => hij h) (fun h => hi h))
        · intro i hi
          rw [hc']
          have hijne : i ≠ j := by rintro rfl; exact hj hi
          rw [Function.update_of_ne hijne]
          exact hon i (Finset.mem_insert_of_mem hi)
      · 
        have hbjf : b j = false := by
          cases hb : b j
          · rfl
          · exact absurd hb hbj
        refine ih c hc ?_ ?_
        · intro i hi
          by_cases hij : i = j
          · subst hij; rw [hcj, hbjf]
          · exact hoff i (fun hmem => (Finset.mem_insert.mp hmem).elim (fun h => hij h) (fun h => hi h))
        · intro i hi; exact hon i (Finset.mem_insert_of_mem hi)


theorem rc80_lower_mono {A : Finset (ConfigSpace ι)} (hA : rc80_IsLower A)
    {a b : ConfigSpace ι} (hab : ∀ i, b i = true → a i = true) (ha : a ∈ A) : b ∈ A := by
  classical
  set D : Finset ι := Finset.univ.filter (fun i => a i = true ∧ b i = false) with hD
  suffices H : ∀ (S : Finset ι) (c : ConfigSpace ι), c ∈ A →
      (∀ i, i ∉ S → c i = b i) → (∀ i ∈ S, c i = true) → b ∈ A by
    refine H D a ha ?_ ?_
    · intro i hi
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
      cases hai : a i
      · 
        have hbif : b i = false := by
          by_contra hbi
          have : b i = true := by
            cases hb : b i
            · exact absurd hb hbi
            · rfl
          rw [hab i this] at hai; exact Bool.noConfusion hai
        rw [hbif]
      · 
        have hbne : b i ≠ false := hi hai
        have : b i = true := by
          cases hbi : b i
          · exact absurd hbi hbne
          · rfl
        rw [this]
    · intro i hi
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi.1
  intro S
  induction S using Finset.induction with
  | empty => intro c hc hoff _
             have : c = b := funext (fun i => hoff i (Finset.notMem_empty i)); rwa [this] at hc
  | @insert j S hj ih =>
      intro c hc hoff hon
      have hcj : c j = true := hon j (Finset.mem_insert_self j S)
      by_cases hbj : b j = false
      · set c' := Function.update c j false with hc'
        have hc'A : c' ∈ A := hA c hc j
        refine ih c' hc'A ?_ ?_
        · intro i hi
          rw [hc']
          by_cases hij : i = j
          · subst hij; rw [Function.update_self]; exact hbj.symm
          · rw [Function.update_of_ne hij]
            exact hoff i (fun hmem => (Finset.mem_insert.mp hmem).elim (fun h => hij h) (fun h => hi h))
        · intro i hi
          rw [hc']
          have hijne : i ≠ j := by rintro rfl; exact hj hi
          rw [Function.update_of_ne hijne]
          exact hon i (Finset.mem_insert_of_mem hi)
      · have hbjt : b j = true := by
          cases hb : b j
          · exact absurd hb hbj
          · rfl
        refine ih c hc ?_ ?_
        · intro i hi
          by_cases hij : i = j
          · subst hij; rw [hcj, hbjt]
          · exact hoff i (fun hmem => (Finset.mem_insert.mp hmem).elim (fun h => hij h) (fun h => hi h))
        · intro i hi; exact hon i (Finset.mem_insert_of_mem hi)


theorem rc80_occ_upper_iff {A : Finset (ConfigSpace ι)} (hA : rc80_IsUpper A)
    (K : Finset ι) (w : ConfigSpace ι) :
    rc80_occ A K w = true ↔ rc80_minext K w ∈ A := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  constructor
  · intro h
    
    exact h (rc80_minext K w) (fun e he => rc80_minext_agree K w he)
  · intro hmin w' hw'
    
    refine rc80_upper_mono hA ?_ hmin
    intro i hi
    
    by_cases hiK : i ∈ K
    · rw [rc80_minext_agree K w hiK] at hi; rw [hw' i hiK]; exact hi
    · simp only [rc80_minext, hiK, if_false] at hi; exact absurd hi (by simp)


theorem rc80_occ_lower_iff {B : Finset (ConfigSpace ι)} (hB : rc80_IsLower B)
    (L : Finset ι) (w : ConfigSpace ι) :
    rc80_occ B L w = true ↔ rc80_maxext L w ∈ B := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  constructor
  · intro h
    exact h (rc80_maxext L w) (fun e he => rc80_maxext_agree L w he)
  · intro hmax w' hw'
    
    refine rc80_lower_mono hB ?_ hmax
    intro i hi
    by_cases hiL : i ∈ L
    · rw [rc80_maxext_agree L w hiL]; rw [hw' i hiL] at hi; exact hi
    · simp only [rc80_maxext, hiL, if_false]


theorem rc80_disjOcc_eq_inter_of_upper_lower {A B : Finset (ConfigSpace ι)}
    (hA : rc80_IsUpper A) (hB : rc80_IsLower B) :
    rc80_disjOccG A B = A ∩ B := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨K, L, _, hK, hL⟩
    rw [rc80_occ_upper_iff hA] at hK
    rw [rc80_occ_lower_iff hB] at hL
    refine ⟨?_, ?_⟩
    · 
      refine rc80_upper_mono hA (fun i hi => rc80_minext_le K w i hi) hK
    · 
      refine rc80_lower_mono hB (fun i hi => rc80_le_maxext L w i hi) hL
  · rintro ⟨hwA, hwB⟩
    refine ⟨Finset.univ.filter (fun i => w i = true), Finset.univ.filter (fun i => w i = false),
      ?_, ?_, ?_⟩
    · 
      rw [Finset.disjoint_filter]
      intro i _ hi
      simp only [hi, Bool.true_eq_false, not_false_eq_true]
    · 
      rw [rc80_occ_upper_iff hA]
      have : rc80_minext (Finset.univ.filter (fun i => w i = true)) w = w := by
        funext i
        simp only [rc80_minext, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hw : w i <;> simp
      rw [this]; exact hwA
    · 
      rw [rc80_occ_lower_iff hB]
      have : rc80_maxext (Finset.univ.filter (fun i => w i = false)) w = w := by
        funext i
        simp only [rc80_maxext, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hw : w i <;> simp
      rw [this]; exact hwB


theorem rc80_wall_upper_lower_iff {A B : Finset (ConfigSpace ι)}
    (hA : rc80_IsUpper A) (hB : rc80_IsLower B) :
    (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card
      ↔ (A ∩ B).card ≤ (rc80_reflInterG A B).card := by
  rw [rc80_disjOcc_eq_inter_of_upper_lower hA hB]


end StatMech.Walls
