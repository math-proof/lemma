/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Def.StatisticalMechanics.Code.Probability.BonamiTensorize.Part4
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bnt_tensorStep_of_vec {ρ : ℝ} (Hvec : bnt_VectorTwoPoint ρ) (n : ℕ)
    (ih : ∀ g : (Fin n → Bool) → ℝ, bnt_qnorm 2 (bnt_noiseOp ρ g) ≤ bnt_qnorm (1 + ρ ^ 2) g)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
  set q : ℝ := 1 + ρ ^ 2 with hqdef
  have hq0 : (0 : ℝ) < q := by rw [hqdef]; positivity
  set g₀ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons false ω') with hg0
  set g₁ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons true ω') with hg1
  set F₀ := bnt_noiseOp ρ g₀ with hF0
  set F₁ := bnt_noiseOp ρ g₁ with hF1
  
  have hcentral : bnt_qnormPow 2 (bnt_noiseOp ρ f)
      = (bnt_qnormPow 2 (fun ω : Fin n → Bool => (1 + ρ) / 2 * F₀ ω + (1 - ρ) / 2 * F₁ ω)
          + bnt_qnormPow 2 (fun ω : Fin n → Bool => (1 - ρ) / 2 * F₀ ω + (1 + ρ) / 2 * F₁ ω)) / 2 := by
    unfold bnt_qnormPow
    rw [bnt_uexp_cons_split (fun x => |bnt_noiseOp ρ f x| ^ (2 : ℝ)), Fintype.sum_bool]
    simp only [bnt_noiseOp_cons_false, bnt_noiseOp_cons_true, hF0, hF1, hg0, hg1]
    rw [add_comm]
  
  have hvec := Hvec n F₀ F₁
  rw [← hqdef] at hvec
  have hstep1 : bnt_qnormPow 2 (bnt_noiseOp ρ f)
      ≤ ((bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2) ^ (2 / q) := by
    rw [hcentral]; exact hvec
  
  have hb0 : bnt_qnorm 2 F₀ ≤ bnt_qnorm q g₀ := ih g₀
  have hb1 : bnt_qnorm 2 F₁ ≤ bnt_qnorm q g₁ := ih g₁
  
  have hpow0 : bnt_qnorm 2 F₀ ^ q ≤ bnt_qnormPow q g₀ := by
    rw [← bnt_qnorm_rpow_self (ne_of_gt hq0) g₀]
    exact Real.rpow_le_rpow (bnt_qnorm_nonneg 2 F₀) hb0 (le_of_lt hq0)
  have hpow1 : bnt_qnorm 2 F₁ ^ q ≤ bnt_qnormPow q g₁ := by
    rw [← bnt_qnorm_rpow_self (ne_of_gt hq0) g₁]
    exact Real.rpow_le_rpow (bnt_qnorm_nonneg 2 F₁) hb1 (le_of_lt hq0)
  
  have hbase : (bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2 ≤ bnt_qnormPow q f := by
    have hsplit : bnt_qnormPow q f = (bnt_qnormPow q g₀ + bnt_qnormPow q g₁) / 2 := by
      rw [bnt_qnormPow_cons_split q f, Fintype.sum_bool, ← hg0, ← hg1]; ring
    rw [hsplit]; linarith
  have hB : (0 : ℝ) ≤ (bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2 := by
    have h0 : (0 : ℝ) ≤ bnt_qnorm 2 F₀ ^ q := Real.rpow_nonneg (bnt_qnorm_nonneg 2 F₀) q
    have h1 : (0 : ℝ) ≤ bnt_qnorm 2 F₁ ^ q := Real.rpow_nonneg (bnt_qnorm_nonneg 2 F₁) q
    linarith
  
  unfold bnt_qnorm
  calc (bnt_qnormPow 2 (bnt_noiseOp ρ f)) ^ ((1 : ℝ) / 2)
      ≤ (((bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2) ^ (2 / q)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (bnt_qnormPow_nonneg 2 _) hstep1 (by norm_num)
    _ = ((bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2) ^ (1 / q) := by
        rw [← Real.rpow_mul hB]; congr 1; field_simp
    _ ≤ (bnt_qnormPow q f) ^ (1 / q) := Real.rpow_le_rpow hB hbase (by positivity)


theorem bnt_TensorStep_of_vectorTwoPoint {ρ : ℝ} (Hvec : bnt_VectorTwoPoint ρ) :
    bnt_TensorStep ρ :=
  fun n ih f => bnt_tensorStep_of_vec Hvec n ih f


theorem bnt_tensorStep_one : bnt_TensorStep 1 := by
  intro n _ f
  have hid : bnt_noiseOp 1 f = f := by funext x; exact bnt_noiseOp_one f x
  rw [hid, show (1 : ℝ) + 1 ^ 2 = 2 by norm_num]


theorem bnt_qnorm_fin_zero {q : ℝ} (hq : 0 < q) (f : (Fin 0 → Bool) → ℝ) :
    bnt_qnorm q f = |f default| := by
  unfold bnt_qnorm bnt_qnormPow bnt_uexp
  rw [show Fintype.card (Fin 0) = 0 by simp, pow_zero, div_one]
  rw [Finset.sum_eq_single (default : Fin 0 → Bool)]
  · rw [← Real.rpow_mul (abs_nonneg _), mul_one_div, div_self (ne_of_gt hq), Real.rpow_one]
  · intro y _ hy; exact absurd (Subsingleton.elim y default) hy
  · intro h; exact absurd (Finset.mem_univ _) h


theorem bnt_noiseOp_fin_zero (ρ : ℝ) (f : (Fin 0 → Bool) → ℝ) :
    bnt_noiseOp ρ f = f := by
  funext x
  unfold bnt_noiseOp bnt_noiseKernel
  rw [Finset.sum_eq_single x]
  · rw [Finset.prod_eq_one (fun i _ => by exact absurd i.2 (by simp)), one_mul]
  · intro y _ hyx; exact absurd (Subsingleton.elim y x) hyx
  · intro h; exact absurd (Finset.mem_univ x) h


theorem bnt_hypercontractivity_fin_zero (ρ : ℝ) (f : (Fin 0 → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
  rw [bnt_noiseOp_fin_zero ρ f, bnt_qnorm_fin_zero (by norm_num),
    bnt_qnorm_fin_zero (by positivity)]


theorem bnt_hypercontractivity {ρ : ℝ} (Hvec : bnt_VectorTwoPoint ρ) (n : ℕ)
    (f : (Fin n → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
  induction n with
  | zero => exact bnt_hypercontractivity_fin_zero ρ f
  | succ m ih => exact bnt_tensorStep_of_vec Hvec m (fun g => ih g) f


theorem bnt_hypercontractivity_of_twoPoint {ρ : ℝ} (Hstep : bnt_TensorStep ρ)
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
  induction n with
  | zero => exact bnt_hypercontractivity_fin_zero ρ f
  | succ m ih => exact Hstep m (fun g => ih g) f


end Probability
end StatMech
