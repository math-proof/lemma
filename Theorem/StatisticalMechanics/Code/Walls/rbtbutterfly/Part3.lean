/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.WellFoundedSet
import Def.StatisticalMechanics.Code.Walls.rbtbutterfly.Part3
open Finset
open scoped BigOperators


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false


theorem rbt_e_perp_g {m : ℕ} (x y z : rbt_Q m) (hx : ¬ rbt_inRed y z x) :
    rbt_inner (rbt_e x) (rbt_g y z) = 0 := by
  rw [rbt_e, rbt_g, rbt_tens_inner]
  rw [rbt_inRed, rbt_inCube, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  push Not at hi
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hy : y i = !(x i) := by cases hxy : x i <;> cases hyi : y i <;> simp_all
  have hz : z i = !(x i) := by cases hxy : x i <;> cases hzi : z i <;> simp_all
  rw [hy, hz]; exact rbt_inner2_e_g (x i)


theorem rbt_f_perp_g {m : ℕ} (x y z : rbt_Q m) (hx : ¬ rbt_inYellow y z x) :
    rbt_inner (rbt_f x) (rbt_g y z) = 0 := by
  rw [rbt_f, rbt_g, rbt_tens_inner]
  rw [rbt_inYellow, rbt_inCube, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  push Not at hi
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hy : y i = !(x i) := by cases hxy : x i <;> cases hyi : y i <;> simp_all
  have hz : z i = x i := by
    have := hi.2
    simp only [rbt_antipode] at this
    cases hxy : x i <;> cases hzi : z i <;> simp_all
  rw [hy, hz]; exact rbt_inner2_f_g (x i)


open Classical in


theorem rbt_triangular_indep {ι : Type*} [Fintype ι] [PartialOrder ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hoff : ∀ x z, ¬ x ≤ z → M x z = 0) (hdiag : ∀ x, M x x ≠ 0) :
    LinearIndependent ℝ (fun x : ι => (fun z => M x z : ι → ℝ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  
  have hcz : ∀ z, ∑ x, c x * M x z = 0 := by
    intro z
    have := congrFun hc z
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  
  intro z
  induction z using WellFoundedLT.induction with
  | _ z ih =>
    
    
    have hsum := hcz z
    have hkey : c z * M z z = 0 := by
      have : (∑ x, c x * M x z) = c z * M z z := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z)]
        have hzero : (∑ x ∈ Finset.univ.erase z, c x * M x z) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hxz : x ≠ z := (Finset.mem_erase.mp hx).1
          by_cases hle : x ≤ z
          · 
            have hlt : x < z := lt_of_le_of_ne hle hxz
            rw [ih x hlt, zero_mul]
          · rw [hoff x z hle, mul_zero]
        rw [hzero, zero_add]
      rw [← this]; exact hsum
    exact (mul_eq_zero.mp hkey).resolve_right (hdiag z)


lemma rbt_e2_eq_zeta (c c' : Bool) : rbt_e2 c c' = if c ≤ c' then 1 else 0 := by
  cases c <;> cases c' <;> simp [rbt_e2]

open Classical in

theorem rbt_e_apply {m : ℕ} (x z : rbt_Q m) :
    rbt_e x z = if x ≤ z then 1 else 0 := by
  simp only [rbt_e, rbt_tens, rbt_e2_eq_zeta]
  by_cases hxz : x ≤ z
  · rw [if_pos hxz]
    apply Finset.prod_eq_one
    intro i _
    rw [if_pos (hxz i)]
  · rw [if_neg hxz]
    rw [Pi.le_def, not_forall] at hxz
    obtain ⟨i, hi⟩ := hxz
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg hi]

open Classical in

lemma rbt_e_off {m : ℕ} (x z : rbt_Q m) (h : ¬ x ≤ z) : rbt_e x z = 0 := by
  rw [rbt_e_apply, if_neg h]

open Classical in

lemma rbt_e_diag {m : ℕ} (x : rbt_Q m) : rbt_e x x ≠ 0 := by
  rw [rbt_e_apply, if_pos le_rfl]; exact one_ne_zero


theorem rbt_e_indep (m : ℕ) : LinearIndependent ℝ (fun x : rbt_Q m => rbt_e x) :=
  rbt_triangular_indep (fun x z => rbt_e x z) (fun x z h => rbt_e_off x z h) rbt_e_diag


lemma rbt_f2_off (c c' : Bool) (h : ¬ c' ≤ c) : rbt_f2 c c' = 0 := by
  cases c <;> cases c' <;> simp_all [rbt_f2]


lemma rbt_f2_diag (c : Bool) : rbt_f2 c c ≠ 0 := by
  cases c <;> simp [rbt_f2]


lemma rbt_f_off {m : ℕ} (x z : rbt_Q m) (h : ¬ z ≤ x) : rbt_f x z = 0 := by
  simp only [rbt_f, rbt_tens]
  rw [Pi.le_def, not_forall] at h
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (rbt_f2_off (x i) (z i) hi)


lemma rbt_f_diag {m : ℕ} (x : rbt_Q m) : rbt_f x x ≠ 0 := by
  simp only [rbt_f, rbt_tens]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => rbt_f2_diag (x i))


theorem rbt_f_indep (m : ℕ) : LinearIndependent ℝ (fun x : rbt_Q m => rbt_f x) := by
  
  have h := rbt_triangular_indep
    (ι := (rbt_Q m)ᵒᵈ)
    (M := fun x z => rbt_f (OrderDual.ofDual x) (OrderDual.ofDual z))
    (fun x z hxz => rbt_f_off _ _ (by
      
      simpa [OrderDual.toDual_le_toDual] using hxz))
    (fun x => rbt_f_diag _)
  
  exact h


end StatMech.Walls.Reimer
