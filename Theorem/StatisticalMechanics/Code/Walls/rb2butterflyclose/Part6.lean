/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rbtbutterfly.Part4
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Extension.Linear
import Def.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part5
open Finset
open scoped BigOperators


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unnecessarySeqFocus false

set_option linter.unusedSimpArgs false

set_option linter.unusedFintypeInType false

set_option maxHeartbeats 1200000


section rb2_part6

open Matrix

open Classical

lemma rb2_Mr_det_ne_zero {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    (rb2_Mr body T).det ≠ 0 := by
  have hmap : rb2_Mr body T = (rb2_Mz body T).map (Int.castRingHom ℝ) := by
    funext y z
    simp only [rb2_Mr, rb2_Mz, Matrix.map_apply, Int.coe_castRingHom, Int.cast_prod, rb2_C]
  have hdet : (rb2_Mr body T).det = ((rb2_Mz body T).det : ℝ) := by
    have hd := RingHom.map_det (Int.castRingHom ℝ) (rb2_Mz body T)
    rw [RingHom.mapMatrix_apply] at hd
    rw [hmap, ← hd]; rfl
  rw [hdet]
  exact_mod_cast rb2_Mz_det_ne_zero body T


theorem rb2_g_indep {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    LinearIndependent ℝ (fun y : T => rbt_g (body (y : rbt_Q m)) (y : rbt_Q m)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  
  have hc2 : ∑ z : rbt_Q m, (∑ y : T, c y * (∏ i, rb2_C (body (y:rbt_Q m) i) ((y:rbt_Q m) i) (z i))) • rb2_hbasis z = 0 := by
    rw [← hc]
    
    have step1 : ∀ z : rbt_Q m,
        (∑ y : T, c y * (∏ i, rb2_C (body (y:rbt_Q m) i) ((y:rbt_Q m) i) (z i))) • rb2_hbasis z
        = ∑ y : T, (c y * (∏ i, rb2_C (body (y:rbt_Q m) i) ((y:rbt_Q m) i) (z i))) • rb2_hbasis z := by
      intro z; rw [Finset.sum_smul]
    rw [Finset.sum_congr rfl (fun z _ => step1 z)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [rb2_g_decomp (body (y:rbt_Q m)) (y:rbt_Q m), Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [smul_smul]
  
  have hzero := (Fintype.linearIndependent_iff.mp (rb2_hbasis_indep m)
    (fun z => ∑ y : T, c y * (∏ i, rb2_C (body (y:rbt_Q m) i) ((y:rbt_Q m) i) (z i))) hc2)
  
  have hMrU : IsUnit (rb2_Mr body T) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (rb2_Mr_det_ne_zero body T)
  have hvec : (c ᵥ* (rb2_Mr body T)) = 0 := by
    funext z
    have := hzero (z : rbt_Q m)
    simp only [Matrix.vecMul, dotProduct, rb2_Mr, Pi.zero_apply]
    rw [← this]
  have : c = 0 := by
    have hinj := (Matrix.vecMul_injective_iff_isUnit).2 hMrU
    have : c ᵥ* (rb2_Mr body T) = (0 : T → ℝ) ᵥ* (rb2_Mr body T) := by rw [hvec]; simp
    exact hinj this
  intro y
  have := congrFun this y
  simpa using this

end rb2_part6


lemma rb2_inner_sum_right {m : ℕ} {ι : Type*} [Fintype ι]
    (A : rbt_Q m → ℝ) (c : ι → ℝ) (v : ι → (rbt_Q m → ℝ)) :
    rbt_inner A (∑ i, c i • v i) = ∑ i, c i * rbt_inner A (v i) := by
  simp only [rbt_inner]
  have : ∀ z, A z * (∑ i, c i • v i) z = ∑ i, c i * (A z * v i z) := by
    intro z
    rw [Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp [Pi.smul_apply, smul_eq_mul]; ring
  simp only [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]


lemma rb2_inner_sum_left {m : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → (rbt_Q m → ℝ)) (A : rbt_Q m → ℝ) :
    rbt_inner (∑ i, c i • v i) A = ∑ i, c i * rbt_inner (v i) A := by
  simp only [rbt_inner]
  have : ∀ z, (∑ i, c i • v i) z * A z = ∑ i, c i * (v i z * A z) := by
    intro z
    rw [Finset.sum_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    simp [Pi.smul_apply, smul_eq_mul]; ring
  simp only [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]


lemma rb2_inner_self_eq_zero {m : ℕ} (A : rbt_Q m → ℝ) :
    rbt_inner A A = 0 ↔ A = 0 := by
  constructor
  · intro h
    funext z
    by_contra hz
    have hpos : (0 : ℝ) < rbt_inner A A := by
      rw [rbt_inner]
      apply Finset.sum_pos'
      · intro i _; exact mul_self_nonneg _
      · exact ⟨z, Finset.mem_univ z, mul_self_pos.mpr hz⟩
    exact absurd h (ne_of_gt hpos)
  · intro h; simp [rbt_inner, h]


theorem rb2_orthUnion3 {m : ℕ} {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (A : α → (rbt_Q m → ℝ)) (B : β → (rbt_Q m → ℝ)) (C : γ → (rbt_Q m → ℝ))
    (hA : LinearIndependent ℝ A) (hB : LinearIndependent ℝ B) (hC : LinearIndependent ℝ C)
    (hAB : ∀ a b, rbt_inner (A a) (B b) = 0)
    (hAC : ∀ a c, rbt_inner (A a) (C c) = 0)
    (hBC : ∀ b c, rbt_inner (B b) (C c) = 0) :
    LinearIndependent ℝ (Sum.elim A (Sum.elim B C)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro d hd
  
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hd
  simp only [Sum.elim_inl, Sum.elim_inr] at hd
  set u := ∑ a, d (Sum.inl a) • A a with hu
  set v := ∑ b, d (Sum.inr (Sum.inl b)) • B b with hv
  set w := ∑ c, d (Sum.inr (Sum.inr c)) • C c with hw
  
  
  have huv : rbt_inner u v = 0 := by
    rw [hu, rb2_inner_sum_left]
    apply Finset.sum_eq_zero; intro a _
    rw [hv, rb2_inner_sum_right]
    simp [hAB a]
  have huw : rbt_inner u w = 0 := by
    rw [hu, rb2_inner_sum_left]
    apply Finset.sum_eq_zero; intro a _
    rw [hw, rb2_inner_sum_right]
    simp [hAC a]
  have hvw : rbt_inner v w = 0 := by
    rw [hv, rb2_inner_sum_left]
    apply Finset.sum_eq_zero; intro b _
    rw [hw, rb2_inner_sum_right]
    simp [hBC b]
  
  have hsymm : ∀ (P R : rbt_Q m → ℝ), rbt_inner P R = rbt_inner R P := by
    intro P R; simp only [rbt_inner]; apply Finset.sum_congr rfl; intro z _; ring
  
  have hdsum : u + v + w = 0 := by rw [add_assoc]; exact hd
  have huu : rbt_inner u u = 0 := by
    have : rbt_inner u (u + v + w) = 0 := by rw [hdsum]; simp [rbt_inner]
    have hexp : rbt_inner u (u + v + w) = rbt_inner u u + rbt_inner u v + rbt_inner u w := by
      simp only [rbt_inner]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro z _
      simp [Pi.add_apply]; ring
    rw [hexp, huv, huw] at this; linarith
  have hvv : rbt_inner v v = 0 := by
    have : rbt_inner v (u + v + w) = 0 := by rw [hdsum]; simp [rbt_inner]
    have hexp : rbt_inner v (u + v + w) = rbt_inner v u + rbt_inner v v + rbt_inner v w := by
      simp only [rbt_inner]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro z _
      simp [Pi.add_apply]; ring
    rw [hexp, hsymm v u, huv, hvw] at this; linarith
  have hww : rbt_inner w w = 0 := by
    have : rbt_inner w (u + v + w) = 0 := by rw [hdsum]; simp [rbt_inner]
    have hexp : rbt_inner w (u + v + w) = rbt_inner w u + rbt_inner w v + rbt_inner w w := by
      simp only [rbt_inner]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro z _
      simp [Pi.add_apply]; ring
    rw [hexp, hsymm w u, huw, hsymm w v, hvw] at this; linarith
  have hu0 : u = 0 := (rb2_inner_self_eq_zero u).mp huu
  have hv0 : v = 0 := (rb2_inner_self_eq_zero v).mp hvv
  have hw0 : w = 0 := (rb2_inner_self_eq_zero w).mp hww
  
  rw [Fintype.linearIndependent_iff] at hA hB hC
  have hda := hA (fun a => d (Sum.inl a)) (by rw [← hu]; exact hu0)
  have hdb := hB (fun b => d (Sum.inr (Sum.inl b))) (by rw [← hv]; exact hv0)
  have hdc := hC (fun c => d (Sum.inr (Sum.inr c))) (by rw [← hw]; exact hw0)
  intro i
  cases i with
  | inl a => exact hda a
  | inr j => cases j with
    | inl b => exact hdb b
    | inr c => exact hdc c


open Classical in


theorem rb2_butterflyLinIndep_of_gIndep (hG : rbt_G_indep) : rbt_ButterflyLinIndep := by
  intro m body T
  
  have hfY : LinearIndependent ℝ (fun x : rbt_Ybar body T => rbt_f (m := m) ↑x) :=
    (rbt_f_indep m).comp (Subtype.val : rbt_Ybar body T → rbt_Q m) Subtype.coe_injective
  have heR : LinearIndependent ℝ (fun x : rbt_Rbar body T => rbt_e (m := m) ↑x) :=
    (rbt_e_indep m).comp (Subtype.val : rbt_Rbar body T → rbt_Q m) Subtype.coe_injective
  
  have hgT : LinearIndependent ℝ (fun y : T => rbt_g (body ↑y) ↑y) := hG m body T
  
  have hsymm : ∀ (P R : rbt_Q m → ℝ), rbt_inner P R = rbt_inner R P := by
    intro P R; simp only [rbt_inner]; apply Finset.sum_congr rfl; intro z _; ring
  apply rb2_orthUnion3 _ _ _ hgT hfY heR
  · 
    intro y x
    rw [hsymm]
    apply rbt_f_perp_g
    
    have hx : (↑x : rbt_Q m) ∉ rbt_Yellow body T := by
      have h2 := x.2; simp only [rbt_Ybar, Finset.mem_sdiff] at h2; exact h2.2
    intro hin
    apply hx
    simp only [rbt_Yellow, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨↑y, y.2, hin⟩⟩
  · 
    intro y x
    rw [hsymm]
    apply rbt_e_perp_g
    have hx : (↑x : rbt_Q m) ∉ rbt_Red body T := by
      have h2 := x.2; simp only [rbt_Rbar, Finset.mem_sdiff] at h2; exact h2.2
    intro hin
    apply hx
    simp only [rbt_Red, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨↑y, y.2, hin⟩⟩
  · 
    intro x x'
    rw [hsymm]
    apply rbt_e_perp_f
    
    have hx' : (↑x' : rbt_Q m) ∈ rbt_Yellow body T := by
      have h2 := x'.2; simp only [rbt_Rbar, Finset.mem_sdiff] at h2; exact h2.1
    have hx : (↑x : rbt_Q m) ∉ rbt_Yellow body T := by
      have h2 := x.2; simp only [rbt_Ybar, Finset.mem_sdiff] at h2; exact h2.2
    intro hcon
    apply hx; rw [← hcon]; exact hx'


theorem rb2_butterfly (hLI : rbt_ButterflyLinIndep) (m : ℕ)
    (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    T.card ≤ (rbt_Red body T ∩ rbt_Yellow body T).card := by
  classical
  
  have hcard := (hLI m body T).fintype_card_le_finrank
  rw [rb2_finrank_Q] at hcard
  
  rw [Fintype.card_sum, Fintype.card_sum] at hcard
  simp only [Fintype.card_coe] at hcard
  
  
  have hpart := rbt_partition_card body T
  omega


theorem rb2_G_indep : rbt_G_indep := fun _ body T => rb2_g_indep body T


theorem rb2_butterflyLinIndep : rbt_ButterflyLinIndep :=
  rb2_butterflyLinIndep_of_gIndep rb2_G_indep


theorem rb2_butterfly_thm (m : ℕ) (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    T.card ≤ (rbt_Red body T ∩ rbt_Yellow body T).card :=
  rb2_butterfly rb2_butterflyLinIndep m body T


end StatMech.Walls.Reimer
