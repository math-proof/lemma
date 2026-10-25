/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part5
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_coeff_empty (p : ℝ) (f : ConfigSpace ι → ℝ) :
    ptn_coeff p f ∅ = OSSS.expect (OSSS.bernoulliWeight p) f := by
  unfold ptn_coeff; congr 1; funext ω; rw [ptn_pchar_empty, mul_one]

omit [DecidableEq ι] in


theorem ptn_repro_kernel {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x y : ConfigSpace ι) :
    (∑ S : Finset ι, ptn_pchar p S x * ptn_pchar p S y)
      = if x = y then 1 / OSSS.weight (OSSS.bernoulliWeight p) x else 0 := by
  have hσ2 : ptn_sigma p ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  have hpt : ∀ S : Finset ι, ptn_pchar p S x * ptn_pchar p S y
      = ∏ i ∈ S, (ptn_psi p (x i) * ptn_psi p (y i)) := by
    intro S; unfold ptn_pchar; rw [← Finset.prod_mul_distrib]
  simp_rw [hpt]
  have hpow : (univ : Finset (Finset ι)) = (univ : Finset ι).powerset := by ext S; simp
  rw [hpow, ← Finset.prod_one_add]
  have h1p : (0:ℝ) < 1 - p := by linarith
  
  have hpsi0sq : ptn_psi p false ^ 2 = p / (1 - p) := by
    unfold ptn_psi; rw [div_pow, ptn_val_false, hσ2]
    rw [show ((0:ℝ) - p) ^ 2 = p ^ 2 by ring]
    rw [pow_two, mul_div_assoc]
    field_simp
  have hpsi1sq : ptn_psi p true ^ 2 = (1 - p) / p := by
    unfold ptn_psi; rw [div_pow, ptn_val_true, hσ2]
    rw [pow_two (1 - p)]
    field_simp
  have hpsicross : ptn_psi p false * ptn_psi p true = -1 := by
    unfold ptn_psi; rw [div_mul_div_comm, ptn_val_false, ptn_val_true,
      ← pow_two, hσ2]
    rw [show ((0:ℝ) - p) * (1 - p) = -(p * (1-p)) by ring]
    rw [neg_div, div_self (by nlinarith)]
  
  have hfac : ∀ i : ι, (1 + ptn_psi p (x i) * ptn_psi p (y i))
      = if x i = y i then 1 / (if x i then p else 1 - p) else 0 := by
    intro i
    cases hx : x i <;> cases hy : y i <;>
      simp only [Bool.false_eq_true, if_true, if_false, Bool.true_eq_false]
    · 
      rw [show ptn_psi p false * ptn_psi p false = ptn_psi p false ^ 2 by ring, hpsi0sq]
      field_simp; ring
    · 
      rw [hpsicross]; ring
    · 
      rw [mul_comm, hpsicross]; ring
    · 
      rw [show ptn_psi p true * ptn_psi p true = ptn_psi p true ^ 2 by ring, hpsi1sq]
      field_simp; ring
  simp_rw [hfac]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    rw [show OSSS.weight (OSSS.bernoulliWeight p) x = ∏ i : ι, (if x i then p else 1 - p) from rfl]
    simp only [one_div, if_true]
    rw [← Finset.prod_inv_distrib]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])


theorem ptn_expansion {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : ConfigSpace ι → ℝ) (x : ConfigSpace ι) :
    (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S x) = f x := by
  calc (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S x)
      = ∑ S : Finset ι,
          (∑ y : ConfigSpace ι, OSSS.weight (OSSS.bernoulliWeight p) y * (f y * ptn_pchar p S y))
            * ptn_pchar p S x := by
        apply Finset.sum_congr rfl; intro S _; rfl
    _ = ∑ y : ConfigSpace ι, OSSS.weight (OSSS.bernoulliWeight p) y * f y
          * (∑ S : Finset ι, ptn_pchar p S y * ptn_pchar p S x) := by
        rw [show (∑ S : Finset ι, (∑ y : ConfigSpace ι,
              OSSS.weight (OSSS.bernoulliWeight p) y * (f y * ptn_pchar p S y)) * ptn_pchar p S x)
            = ∑ S : Finset ι, ∑ y : ConfigSpace ι,
              OSSS.weight (OSSS.bernoulliWeight p) y * f y * (ptn_pchar p S y * ptn_pchar p S x)
            from by apply Finset.sum_congr rfl; intro S _; rw [Finset.sum_mul];
                    apply Finset.sum_congr rfl; intro y _; ring]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro y _
        rw [Finset.mul_sum]
    _ = ∑ y : ConfigSpace ι, OSSS.weight (OSSS.bernoulliWeight p) y * f y
          * (if y = x then 1 / OSSS.weight (OSSS.bernoulliWeight p) y else 0) := by
        apply Finset.sum_congr rfl; intro y _
        rw [ptn_repro_kernel hp0 hp1 y x]
    _ = f x := by
        rw [Finset.sum_eq_single x]
        · rw [if_pos rfl]
          have hw : OSSS.weight (OSSS.bernoulliWeight p) x ≠ 0 := by
            rw [show OSSS.weight (OSSS.bernoulliWeight p) x = ∏ i : ι, (if x i then p else 1 - p) from rfl]
            apply Finset.prod_ne_zero_iff.mpr
            intro i _; cases x i <;> simp only [Bool.false_eq_true, if_true, if_false] <;>
              first | exact hp0.ne' | (intro h; linarith)
          field_simp
        · intro y _ hyx; rw [if_neg hyx, mul_zero]
        · intro h; exact absurd (Finset.mem_univ x) h


theorem ptn_expect_finsetSum {κ : Type*} (p : ℝ) (s : Finset κ) (g : κ → ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ∑ k ∈ s, g k ω)
      = ∑ k ∈ s, OSSS.expect (OSSS.bernoulliWeight p) (g k) := by
  unfold OSSS.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]


theorem ptn_parseval {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f g : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => f ω * g ω)
      = ∑ S : Finset ι, ptn_coeff p f S * ptn_coeff p g S := by
  
  have hf : (fun ω : ConfigSpace ι => f ω * g ω)
      = (fun ω => (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S ω)
                  * (∑ T : Finset ι, ptn_coeff p g T * ptn_pchar p T ω)) := by
    funext ω; rw [ptn_expansion hp0 hp1 f ω, ptn_expansion hp0 hp1 g ω]
  rw [hf]
  
  have hdist : (fun ω : ConfigSpace ι =>
        (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S ω)
          * (∑ T : Finset ι, ptn_coeff p g T * ptn_pchar p T ω))
      = (fun ω => ∑ S : Finset ι, ∑ T : Finset ι,
          (ptn_coeff p f S * ptn_coeff p g T) * (ptn_pchar p S ω * ptn_pchar p T ω)) := by
    funext ω; rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro T _; ring
  rw [hdist, ptn_expect_finsetSum]
  apply Finset.sum_congr rfl; intro S _
  rw [ptn_expect_finsetSum]
  have hterm : ∀ T ∈ (univ : Finset (Finset ι)),
      OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => ptn_coeff p f S * ptn_coeff p g T * (ptn_pchar p S ω * ptn_pchar p T ω))
        = ptn_coeff p f S * ptn_coeff p g T * (if S = T then 1 else 0) := by
    intro T _
    rw [OSSS.expect_const_mul, ptn_orthonormal hp0 hp1 S T]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem S (Finset.mem_univ S)]
  · rw [if_pos rfl, mul_one]
  · intro T _ hTS; rw [if_neg (fun h => hTS h.symm), mul_zero]


theorem ptn_parseval_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2)
      = ∑ S : Finset ι, (ptn_coeff p f S) ^ 2 := by
  rw [show (fun ω : ConfigSpace ι => (f ω) ^ 2) = (fun ω => f ω * f ω) from by funext ω; ring]
  rw [ptn_parseval hp0 hp1 f f]
  apply Finset.sum_congr rfl; intro S _; rw [sq]


theorem ptn_var_eq_fourierWeight {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f : ConfigSpace ι → ℝ) :
    OSSS.var (OSSS.bernoulliWeight p) f
      = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
  unfold OSSS.var OSSS.cov
  rw [show (fun ω : ConfigSpace ι => f ω * f ω) = (fun ω => (f ω) ^ 2) from by funext ω; ring]
  rw [ptn_parseval_sq hp0 hp1 f]
  rw [← Finset.add_sum_erase univ (fun S => (ptn_coeff p f S) ^ 2) (Finset.mem_univ (∅ : Finset ι))]
  rw [ptn_coeff_empty]
  ring


theorem ptn_psi_jump {p : ℝ} (_hp0 : 0 < p) (_hp1 : p < 1) :
    ptn_psi p true - ptn_psi p false = 1 / ptn_sigma p := by
  unfold ptn_psi; rw [ptn_val_true, ptn_val_false, div_sub_div_same]
  congr 1; ring

omit [Fintype ι] in


theorem ptn_pchar_deriv {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S : Finset ι) (e : ι)
    (ω : ConfigSpace ι) :
    ptn_pchar p S (StatMech.setOpen e ω) - ptn_pchar p S (StatMech.setClosed e ω)
      = if e ∈ S then (1 / ptn_sigma p) * ptn_pchar p (S.erase e) ω else 0 := by
  by_cases he : e ∈ S
  · rw [if_pos he]
    unfold ptn_pchar
    rw [← Finset.prod_erase_mul S _ he, ← Finset.prod_erase_mul S _ he]
    have hprodO : (∏ i ∈ S.erase e, ptn_psi p (StatMech.setOpen e ω i))
        = ∏ i ∈ S.erase e, ptn_psi p (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi; rw [StatMech.setOpen_of_ne (Finset.ne_of_mem_erase hi)]
    have hprodC : (∏ i ∈ S.erase e, ptn_psi p (StatMech.setClosed e ω i))
        = ∏ i ∈ S.erase e, ptn_psi p (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi; rw [StatMech.setClosed_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hprodO, hprodC, StatMech.setOpen_self, StatMech.setClosed_self]
    rw [← mul_sub, ptn_psi_jump hp0 hp1]
    ring
  · rw [if_neg he]
    unfold ptn_pchar
    have : (∏ i ∈ S, ptn_psi p (StatMech.setOpen e ω i))
        = ∏ i ∈ S, ptn_psi p (StatMech.setClosed e ω i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hie : i ≠ e := fun h => he (h ▸ hi)
      rw [StatMech.setOpen_of_ne hie, StatMech.setClosed_of_ne hie]
    rw [this, sub_self]


theorem ptn_deriv_fourier {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : ConfigSpace ι → ℝ) (e : ι) (ω : ConfigSpace ι) :
    f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω)
      = ∑ S ∈ univ.filter (fun S => e ∈ S),
          (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) ω := by
  have hO : f (StatMech.setOpen e ω)
      = ∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S (StatMech.setOpen e ω) := by
    rw [ptn_expansion hp0 hp1]
  have hC : f (StatMech.setClosed e ω)
      = ∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S (StatMech.setClosed e ω) := by
    rw [ptn_expansion hp0 hp1]
  rw [hO, hC, ← Finset.sum_sub_distrib]
  have hterm : ∀ S : Finset ι,
      ptn_coeff p f S * ptn_pchar p S (StatMech.setOpen e ω)
        - ptn_coeff p f S * ptn_pchar p S (StatMech.setClosed e ω)
        = if e ∈ S then (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) ω else 0 := by
    intro S; rw [← mul_sub, ptn_pchar_deriv hp0 hp1]
    by_cases he : e ∈ S
    · rw [if_pos he, if_pos he]; rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]; ring
    · rw [if_neg he, if_neg he, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_filter]


theorem ptn_expect_sum_pchar_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (s : Finset (Finset ι)) (a : Finset ι → ℝ) (T : Finset ι → Finset ι)
    (hTinj : Set.InjOn T s) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => (∑ S ∈ s, a S * ptn_pchar p (T S) ω) ^ 2)
      = ∑ S ∈ s, (a S) ^ 2 := by
  rw [show (fun ω : ConfigSpace ι => (∑ S ∈ s, a S * ptn_pchar p (T S) ω) ^ 2)
      = (fun ω => ∑ S ∈ s, ∑ U ∈ s,
          (a S * a U) * (ptn_pchar p (T S) ω * ptn_pchar p (T U) ω)) from ?_]
  · rw [ptn_expect_finsetSum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [ptn_expect_finsetSum]
    have hterm : ∀ U ∈ s,
        OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω => a S * a U * (ptn_pchar p (T S) ω * ptn_pchar p (T U) ω))
          = a S * a U * (if T S = T U then 1 else 0) := by
      intro U _; rw [OSSS.expect_const_mul, ptn_orthonormal hp0 hp1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem S hS]
    · rw [if_pos rfl, mul_one, sq]
    · intro U hU hUS
      have hne : T S ≠ T U := fun h => hUS (hTinj hU hS h.symm)
      rw [if_neg hne, mul_zero]
  · funext ω; rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro U _; ring


theorem ptn_erase_injOn (e : ι) :
    Set.InjOn (fun S => Finset.erase S e) ↑(univ.filter (fun S : Finset ι => e ∈ S)) := by
  intro S hS U hU h
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS hU
  simp only at h
  rw [← Finset.insert_erase hS, ← Finset.insert_erase hU, h]

omit [Fintype ι] in

theorem ptn_abs_diff_indicator (φ : ConfigSpace ι → Bool) (e : ι) (ω : ConfigSpace ι) :
    |(fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
        - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)|
      = ((fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
        - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)) ^ 2 := by
  simp only
  by_cases hO : φ (StatMech.setOpen e ω) <;> by_cases hC : φ (StatMech.setClosed e ω) <;>
    simp [hO, hC]


theorem ptn_infl_eq_fourierWeight {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) (e : ι) :
    OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e
      = (1 / (ptn_sigma p) ^ 2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set g := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hg
  unfold OSSS.infl
  have habs : (fun ω => |g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)|)
      = (fun ω => (g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)) ^ 2) := by
    funext ω; exact ptn_abs_diff_indicator φ e ω
  rw [habs]
  have hd : (fun ω : ConfigSpace ι => (g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)) ^ 2)
      = (fun ω => (∑ S ∈ univ.filter (fun S => e ∈ S),
          (ptn_coeff p g S / ptn_sigma p) * ptn_pchar p (S.erase e) ω) ^ 2) := by
    funext ω; rw [ptn_deriv_fourier hp0 hp1 g e ω]
  rw [hd, ptn_expect_sum_pchar_sq hp0 hp1 _ _ (fun S => S.erase e) (ptn_erase_injOn e)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [div_pow, one_div, ← div_eq_inv_mul]


theorem ptn_totalInfl_eq_fourierWeight {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  unfold totalInfl
  have hinfl : ∀ e : ι,
      OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e
        = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (if e ∈ S then c S else 0) := by
    intro e; rw [ptn_infl_eq_fourierWeight hp0 hp1, Finset.sum_filter]
  simp_rw [hinfl]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hc, nsmul_eq_mul]


end StatMech.Probability
