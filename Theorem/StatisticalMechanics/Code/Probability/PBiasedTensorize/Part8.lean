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
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part8
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_kop_pchar_apply {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (S : Finset ι)
    (x : ConfigSpace ι) :
    ptn_kop p ρ (ptn_pchar p S) x = ρ ^ S.card * ptn_pchar p S x := by
  have hmean := ptn_psi_mean hp0 hp1
  unfold ptn_kop ptn_kernel ptn_pchar
  
  have hchar : ∀ y : ConfigSpace ι, (∏ i ∈ S, ptn_psi p (y i))
      = ∏ i : ι, (if i ∈ S then ptn_psi p (y i) else 1) := by
    intro y; rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hchar]
  have hcomb : ∀ y : ConfigSpace ι,
      (∏ i : ι, ptn_kbit p ρ (x i) (y i)) * (∏ i : ι, (if i ∈ S then ptn_psi p (y i) else 1))
        = ∏ i : ι, (ptn_kbit p ρ (x i) (y i) * (if i ∈ S then ptn_psi p (y i) else 1)) := by
    intro y; rw [← Finset.prod_mul_distrib]
  simp_rw [hcomb]
  rw [← Fintype.prod_sum (fun (i : ι) (c : Bool) =>
        ptn_kbit p ρ (x i) c * (if i ∈ S then ptn_psi p c else 1))]
  
  have hfac : ∀ i : ι,
      (∑ c : Bool, ptn_kbit p ρ (x i) c * (if i ∈ S then ptn_psi p c else 1))
        = if i ∈ S then ρ * ptn_psi p (x i) else 1 := by
    intro i
    unfold ptn_kbit
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      rw [Fintype.sum_bool]
      cases hx : x i <;>
        simp only [Bool.false_eq_true, if_false, if_true, Bool.true_eq_false] <;>
        linear_combination (1 - ρ) * hmean
    · simp only [hi, if_false, mul_one]
      rw [Fintype.sum_bool]
      cases hx : x i <;>
        simp only [Bool.false_eq_true, if_false, if_true, Bool.true_eq_false] <;> ring
  simp_rw [hfac]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const]


theorem ptn_kop_finsetSum {κ : Type*} (p ρ : ℝ) (s : Finset κ) (g : κ → ConfigSpace ι → ℝ) :
    ptn_kop p ρ (fun x => ∑ k ∈ s, g k x) = fun x => ∑ k ∈ s, ptn_kop p ρ (g k) x := by
  funext x; unfold ptn_kop; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]


theorem ptn_kop_const_mul (p ρ c : ℝ) (g : ConfigSpace ι → ℝ) :
    ptn_kop p ρ (fun x => c * g x) = fun x => c * ptn_kop p ρ g x := by
  funext x; unfold ptn_kop; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _; ring


theorem ptn_kop_eq_noiseOp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (f : ConfigSpace ι → ℝ) :
    ptn_kop p ρ f = ptn_noiseOp p ρ f := by
  have hf : f = (fun x => ∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S x) := by
    funext x; rw [ptn_expansion hp0 hp1]
  conv_lhs => rw [hf]
  rw [ptn_kop_finsetSum]
  funext x
  unfold ptn_noiseOp
  simp_rw [ptn_kop_const_mul p ρ (ptn_coeff p f _) (ptn_pchar p _)]
  apply Finset.sum_congr rfl
  intro S _
  rw [ptn_kop_pchar_apply hp0 hp1]
  ring


theorem ptn_expect_sq_lincomb (p a b : ℝ) (u v : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (a * u ω + b * v ω) ^ 2)
      = a ^ 2 * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2)
        + 2 * a * b * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω)
        + b ^ 2 * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2) := by
  rw [show (fun ω : ConfigSpace ι => (a * u ω + b * v ω) ^ 2)
      = (fun ω => a ^ 2 * (u ω) ^ 2 + (2 * a * b) * (u ω * v ω) + b ^ 2 * (v ω) ^ 2)
    from by funext ω; ring]
  rw [OSSS.expect_add, OSSS.expect_add, OSSS.expect_const_mul, OSSS.expect_const_mul,
    OSSS.expect_const_mul]


theorem ptn_expect_inner_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω)
      ≤ Real.sqrt (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2))
        * Real.sqrt (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2)) := by
  set W := fun ω : ConfigSpace ι => OSSS.weight (OSSS.bernoulliWeight p) ω with hW
  have hWnn : ∀ ω, 0 ≤ W ω := fun ω =>
    Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0 hp1).nonneg e (ω e))
  
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ConfigSpace ι))
    (fun ω => Real.sqrt (W ω) * u ω) (fun ω => Real.sqrt (W ω) * v ω)
  
  have hsqW : ∀ ω, Real.sqrt (W ω) * Real.sqrt (W ω) = W ω := fun ω =>
    Real.mul_self_sqrt (hWnn ω)
  have he1 : (∑ ω : ConfigSpace ι, (Real.sqrt (W ω) * u ω) * (Real.sqrt (W ω) * v ω))
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω) := by
    unfold OSSS.expect; apply Finset.sum_congr rfl
    intro ω _; rw [show (Real.sqrt (W ω) * u ω) * (Real.sqrt (W ω) * v ω)
        = (Real.sqrt (W ω) * Real.sqrt (W ω)) * (u ω * v ω) by ring, hsqW]
  have he2 : (∑ ω : ConfigSpace ι, (Real.sqrt (W ω) * u ω) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2) := by
    unfold OSSS.expect; apply Finset.sum_congr rfl
    intro ω _; rw [mul_pow, Real.sq_sqrt (hWnn ω)]
  have he3 : (∑ ω : ConfigSpace ι, (Real.sqrt (W ω) * v ω) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2) := by
    unfold OSSS.expect; apply Finset.sum_congr rfl
    intro ω _; rw [mul_pow, Real.sq_sqrt (hWnn ω)]
  rw [he1, he2, he3] at hcs
  
  set Euv := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω)
  set Eu := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2) with hEu
  set Ev := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2) with hEv
  have hEunn : 0 ≤ Eu := by
    rw [hEu]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hWnn ω) (sq_nonneg _))
  have hEvnn : 0 ≤ Ev := by
    rw [hEv]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hWnn ω) (sq_nonneg _))
  calc Euv ≤ Real.sqrt (Euv ^ 2) := by rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
    _ ≤ Real.sqrt (Eu * Ev) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt Eu * Real.sqrt Ev := Real.sqrt_mul hEunn Ev


theorem ptn_kernel_cons {n : ℕ} (p ρ : ℝ) (a c : Bool) (ω ω' : Fin n → Bool) :
    ptn_kernel p ρ (Fin.cons a ω) (Fin.cons c ω')
      = ptn_kbit p ρ a c * ptn_kernel p ρ ω ω' := by
  unfold ptn_kernel
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]


theorem ptn_kop_cons {n : ℕ} (p ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) (a : Bool)
    (ω : Fin n → Bool) :
    ptn_kop p ρ f (Fin.cons a ω)
      = ∑ c : Bool, ptn_kbit p ρ a c
          * ptn_kop p ρ (fun ω' : Fin n → Bool => f (Fin.cons c ω')) ω := by
  unfold ptn_kop
  rw [ptn_sum_cons_split (fun y : Fin (n + 1) → Bool => ptn_kernel p ρ (Fin.cons a ω) y * f y)]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω' _
  rw [ptn_kernel_cons]
  ring


theorem ptn_kop_cons_pair {n : ℕ} (p ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) (a : Bool)
    (ω : Fin n → Bool) :
    ptn_kop p ρ f (Fin.cons a ω)
      = ptn_kbit p ρ a false * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω
        + ptn_kbit p ρ a true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω := by
  rw [ptn_kop_cons, Fintype.sum_bool, add_comm]


theorem ptn_kop_fin_zero (p ρ : ℝ) (f : (Fin 0 → Bool) → ℝ) :
    ptn_kop p ρ f = f := by
  funext x
  unfold ptn_kop ptn_kernel
  rw [Finset.sum_eq_single x]
  · rw [Finset.prod_eq_one (fun i _ => absurd i.2 (by simp)), one_mul]
  · intro y _ hyx; exact absurd (Subsingleton.elim y x) hyx
  · intro h; exact absurd (Finset.mem_univ x) h


theorem ptn_qnorm_fin_zero {p q : ℝ} (hq : 0 < q) (f : (Fin 0 → Bool) → ℝ) :
    ptn_qnorm p q f = |f default| := by
  unfold ptn_qnorm ptn_qnormPow OSSS.expect
  rw [Finset.sum_eq_single (default : Fin 0 → Bool)]
  · rw [show OSSS.weight (OSSS.bernoulliWeight p) (default : Fin 0 → Bool) = 1 from by
        unfold OSSS.weight; rw [Finset.prod_eq_one (fun i _ => absurd i.2 (by simp))]]
    simp only [one_mul]
    rw [← Real.rpow_mul (abs_nonneg _), one_div, mul_inv_cancel₀ (ne_of_gt hq), Real.rpow_one]
  · intro y _ hy; exact absurd (Subsingleton.elim y default) hy
  · intro h; exact absurd (Finset.mem_univ _) h


theorem ptn_qnormPow_cons_split {n : ℕ} (p q : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    ptn_qnormPow p q f
      = (1 - p) * ptn_qnormPow p q (fun ω' : Fin n → Bool => f (Fin.cons false ω'))
        + p * ptn_qnormPow p q (fun ω' : Fin n → Bool => f (Fin.cons true ω')) := by
  unfold ptn_qnormPow
  rw [ptn_expect_cons_split p (fun ω => |f ω| ^ q)]


theorem ptn_kbit_ff (p ρ : ℝ) : ptn_kbit p ρ false false = ρ + (1 - ρ) * (1 - p) := by
  unfold ptn_kbit; norm_num

theorem ptn_kbit_ft (p ρ : ℝ) : ptn_kbit p ρ false true = (1 - ρ) * p := by
  unfold ptn_kbit; norm_num

theorem ptn_kbit_tf (p ρ : ℝ) : ptn_kbit p ρ true false = (1 - ρ) * (1 - p) := by
  unfold ptn_kbit; norm_num

theorem ptn_kbit_tt (p ρ : ℝ) : ptn_kbit p ρ true true = ρ + (1 - ρ) * p := by
  unfold ptn_kbit; norm_num


theorem ptn_kop_l2sq_cons {n : ℕ} (p ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    ptn_qnormPow p 2 (ptn_kop p ρ f)
      = (1 - p) * OSSS.expect (OSSS.bernoulliWeight p)
            (fun ω : Fin n → Bool => (ptn_kbit p ρ false false
              * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω
              + ptn_kbit p ρ false true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω) ^ 2)
        + p * OSSS.expect (OSSS.bernoulliWeight p)
            (fun ω : Fin n → Bool => (ptn_kbit p ρ true false
              * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω
              + ptn_kbit p ρ true true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω) ^ 2) := by
  rw [ptn_qnormPow2_eq_expect_sq, ptn_expect_cons_split p (fun ω => (ptn_kop p ρ f ω) ^ 2)]
  congr 2 <;> · congr 1; funext ω; rw [ptn_kop_cons_pair]


theorem ptn_cons_quadform_eq {p q ρ u v : ℝ} (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
    (1 - p) * (ptn_kbit p ρ false false * u + ptn_kbit p ρ false true * v) ^ 2
        + p * (ptn_kbit p ρ true false * u + ptn_kbit p ρ true true * v) ^ 2
      = ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2 := by
  rw [ptn_kbit_ff, ptn_kbit_ft, ptn_kbit_tf, ptn_kbit_tt]
  linear_combination (p * (1 - p) * (u - v) ^ 2) * hρsq


theorem ptn_kbit_nonneg {p ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a c : Bool) : 0 ≤ ptn_kbit p ρ a c := by
  cases a <;> cases c <;>
    simp only [ptn_kbit_ff, ptn_kbit_ft, ptn_kbit_tf, ptn_kbit_tt] <;> nlinarith


theorem ptn_tensorStep {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) (n : ℕ)
    (ih : ∀ g : (Fin n → Bool) → ℝ, ptn_qnorm p 2 (ptn_kop p ρ g) ≤ ptn_qnorm p q g)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
  have hq0 : (0 : ℝ) < q := by linarith
  set g₀ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons false ω') with hg0
  set g₁ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons true ω') with hg1
  set F₀ := ptn_kop p ρ g₀ with hF0
  set F₁ := ptn_kop p ρ g₁ with hF1
  set Eu := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => (F₀ ω) ^ 2) with hEu
  set Ev := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => (F₁ ω) ^ 2) with hEv
  set Euv := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => F₀ ω * F₁ ω) with hEuv
  set u := Real.sqrt Eu with hu
  set v := Real.sqrt Ev with hv
  have hEunn : 0 ≤ Eu := by
    rw [hEu]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg
      (Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0.le hp1.le).nonneg e (ω e)))
      (sq_nonneg _))
  have hEvnn : 0 ≤ Ev := by
    rw [hEv]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg
      (Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0.le hp1.le).nonneg e (ω e)))
      (sq_nonneg _))
  have hunn : 0 ≤ u := Real.sqrt_nonneg _
  have hvnn : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = Eu := Real.sq_sqrt hEunn
  have hv2 : v ^ 2 = Ev := Real.sq_sqrt hEvnn
  have hCS : Euv ≤ u * v := by rw [hu, hv]; exact ptn_expect_inner_le hp0.le hp1.le F₀ F₁
  
  have hLHS : ptn_qnormPow p 2 (ptn_kop p ρ f)
      = (1 - p) * (ptn_kbit p ρ false false ^ 2 * Eu
            + 2 * ptn_kbit p ρ false false * ptn_kbit p ρ false true * Euv
            + ptn_kbit p ρ false true ^ 2 * Ev)
        + p * (ptn_kbit p ρ true false ^ 2 * Eu
            + 2 * ptn_kbit p ρ true false * ptn_kbit p ρ true true * Euv
            + ptn_kbit p ρ true true ^ 2 * Ev) := by
    rw [ptn_kop_l2sq_cons]
    rw [ptn_expect_sq_lincomb p (ptn_kbit p ρ false false) (ptn_kbit p ρ false true) F₀ F₁,
        ptn_expect_sq_lincomb p (ptn_kbit p ρ true false) (ptn_kbit p ρ true true) F₀ F₁]
  
  have hcoef0 : 0 ≤ (1 - p) * (2 * ptn_kbit p ρ false false * ptn_kbit p ρ false true) := by
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le false false
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le false true
    positivity
  have hcoef1 : 0 ≤ p * (2 * ptn_kbit p ρ true false * ptn_kbit p ρ true true) := by
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le true false
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le true true
    positivity
  
  set a00 := ptn_kbit p ρ false false with ha00
  set a01 := ptn_kbit p ρ false true with ha01
  set a10 := ptn_kbit p ρ true false with ha10
  set a11 := ptn_kbit p ρ true true with ha11
  have hbound : ptn_qnormPow p 2 (ptn_kop p ρ f)
      ≤ (1 - p) * (a00 * u + a01 * v) ^ 2 + p * (a10 * u + a11 * v) ^ 2 := by
    rw [hLHS]
    have hgoal : (1 - p) * (a00 * u + a01 * v) ^ 2 + p * (a10 * u + a11 * v) ^ 2
        - ((1 - p) * (a00 ^ 2 * Eu + 2 * a00 * a01 * Euv + a01 ^ 2 * Ev)
          + p * (a10 ^ 2 * Eu + 2 * a10 * a11 * Euv + a11 ^ 2 * Ev))
        = (1 - p) * (2 * a00 * a01) * (u * v - Euv) + p * (2 * a10 * a11) * (u * v - Euv) := by
      rw [← hu2, ← hv2]; ring
    have hc0 : 0 ≤ (1 - p) * (2 * a00 * a01) * (u * v - Euv) :=
      mul_nonneg hcoef0 (by linarith [hCS])
    have hc1 : 0 ≤ p * (2 * a10 * a11) * (u * v - Euv) :=
      mul_nonneg hcoef1 (by linarith [hCS])
    linarith [hgoal, hc0, hc1]
  
  have hquad := ptn_cons_quadform_eq (p := p) (q := q) (ρ := ρ) (u := u) (v := v) hρsq
  have hpcx := pcx_two_point_value hp0 hp1 hq1 hq2 u v
  rw [abs_of_nonneg hunn, abs_of_nonneg hvnn] at hpcx
  have hstep1 : ptn_qnormPow p 2 (ptn_kop p ρ f)
      ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
    refine le_trans hbound ?_
    rw [hquad]; exact hpcx
  
  have hub : u ≤ ptn_qnorm p q g₀ := by
    have hsq : Eu = (ptn_qnorm p 2 F₀) ^ 2 := by
      rw [hEu, ← ptn_qnormPow2_eq_expect_sq, ptn_qnorm2_sq hp0.le hp1.le F₀]
    rw [hu, hsq, Real.sqrt_sq (ptn_qnorm_nonneg hp0.le hp1.le 2 F₀)]
    exact ih g₀
  have hvb : v ≤ ptn_qnorm p q g₁ := by
    have hsq : Ev = (ptn_qnorm p 2 F₁) ^ 2 := by
      rw [hEv, ← ptn_qnormPow2_eq_expect_sq, ptn_qnorm2_sq hp0.le hp1.le F₁]
    rw [hv, hsq, Real.sqrt_sq (ptn_qnorm_nonneg hp0.le hp1.le 2 F₁)]
    exact ih g₁
  have huq : u ^ q ≤ ptn_qnormPow p q g₀ := by
    rw [← ptn_qnorm_rpow_self hp0.le hp1.le (ne_of_gt hq0) g₀]
    exact Real.rpow_le_rpow hunn hub hq0.le
  have hvq : v ^ q ≤ ptn_qnormPow p q g₁ := by
    rw [← ptn_qnorm_rpow_self hp0.le hp1.le (ne_of_gt hq0) g₁]
    exact Real.rpow_le_rpow hvnn hvb hq0.le
  have hbasebound : (1 - p) * u ^ q + p * v ^ q ≤ ptn_qnormPow p q f := by
    rw [ptn_qnormPow_cons_split p q f, ← hg0, ← hg1]
    have h1p : 0 ≤ 1 - p := by linarith
    have hA := mul_le_mul_of_nonneg_left huq h1p
    have hB := mul_le_mul_of_nonneg_left hvq hp0.le
    linarith
  have hBnn : (0 : ℝ) ≤ (1 - p) * u ^ q + p * v ^ q := by
    have : (0:ℝ) ≤ u ^ q := Real.rpow_nonneg hunn q
    have : (0:ℝ) ≤ v ^ q := Real.rpow_nonneg hvnn q
    have h1p : 0 ≤ 1 - p := by linarith
    positivity
  
  have hstep2 : ptn_qnormPow p 2 (ptn_kop p ρ f) ≤ (ptn_qnormPow p q f) ^ (2 / q) := by
    refine le_trans hstep1 ?_
    exact Real.rpow_le_rpow hBnn hbasebound (by positivity)
  
  unfold ptn_qnorm
  calc (ptn_qnormPow p 2 (ptn_kop p ρ f)) ^ (1 / (2:ℝ))
      ≤ ((ptn_qnormPow p q f) ^ (2 / q)) ^ (1 / (2:ℝ)) :=
        Real.rpow_le_rpow (ptn_qnormPow_nonneg hp0.le hp1.le 2 _) hstep2 (by norm_num)
    _ = (ptn_qnormPow p q f) ^ (1 / q) := by
        rw [← Real.rpow_mul (ptn_qnormPow_nonneg hp0.le hp1.le q f)]
        congr 1; field_simp


theorem ptn_hypercontractivity_fin {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
  induction n with
  | zero =>
    rw [ptn_kop_fin_zero, ptn_qnorm_fin_zero (by norm_num : (0:ℝ) < 2),
        ptn_qnorm_fin_zero (by linarith : (0:ℝ) < q)]
  | succ m ih => exact ptn_tensorStep hp0 hp1 h0 h1 hq1 hq2 hρsq m (fun g => ih g) f


theorem ptn_lowDegreeWeight_fin {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    (∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2)
      ≤ (ptn_qnorm p q f) ^ 2 := by
  have hhc := ptn_hypercontractivity_fin hp0 hp1 h0 h1 hq1 hq2 hρsq n f
  have hlhsnn : 0 ≤ ptn_qnorm p 2 (ptn_kop p ρ f) := ptn_qnorm_nonneg hp0.le hp1.le 2 _
  have hrhsnn : 0 ≤ ptn_qnorm p q f := ptn_qnorm_nonneg hp0.le hp1.le q f
  have hsq : (ptn_qnorm p 2 (ptn_kop p ρ f)) ^ 2 ≤ (ptn_qnorm p q f) ^ 2 := by
    nlinarith [hhc, hlhsnn, hrhsnn]
  rw [ptn_qnorm2_sq hp0.le hp1.le, ptn_qnormPow2_eq_expect_sq, ptn_kop_eq_noiseOp hp0 hp1,
      ptn_noiseOp_l2sq hp0 hp1] at hsq
  exact hsq


end StatMech.Probability
