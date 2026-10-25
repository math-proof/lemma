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
import Def.StatisticalMechanics.Code.Probability.BonamiTensorize.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bnt_noiseOp_one (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    bnt_noiseOp 1 f x = f x := by
  unfold bnt_noiseOp bnt_noiseKernel
  have hker : ∀ y : ι → Bool,
      (∏ i : ι, (if x i = y i then (1 + (1 : ℝ)) / 2 else (1 - 1) / 2))
        = (if x = y then 1 else 0) := by
    intro y
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg hxy, Finset.prod_eq_zero_iff]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
      exact ⟨i, mem_univ i, by simp [hi]⟩
  simp_rw [hker, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq univ x (fun y => f y)]
  simp


theorem bnt_sum_cons_split {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin (n + 1) → Bool) → M) :
    (∑ y : Fin (n + 1) → Bool, F y)
      = ∑ c : Bool, ∑ ω' : Fin n → Bool, F (Fin.cons c ω') := by
  rw [← Fintype.sum_prod_type (fun p : Bool × (Fin n → Bool) => F (Fin.cons p.1 p.2))]
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool))
    (fun p => F (Fin.cons p.1 p.2)) F (fun _ => rfl)).symm


theorem bnt_uexp_cons_split {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    bnt_uexp f
      = (∑ c : Bool, bnt_uexp (fun ω' : Fin n → Bool => f (Fin.cons c ω'))) / 2 := by
  unfold bnt_uexp
  rw [bnt_sum_cons_split f, Fintype.card_fin, Fintype.card_fin, pow_succ,
    Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [div_div]


theorem bnt_noiseOp_cons {n : ℕ} (ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ)
    (a : Bool) (ω : Fin n → Bool) :
    bnt_noiseOp ρ f (Fin.cons a ω)
      = ∑ c : Bool, (if a = c then (1 + ρ) / 2 else (1 - ρ) / 2)
          * bnt_noiseOp ρ (fun ω' : Fin n → Bool => f (Fin.cons c ω')) ω := by
  unfold bnt_noiseOp bnt_noiseKernel
  set xa : Fin (n + 1) → Bool := Fin.cons a ω with hxa
  refine (bnt_sum_cons_split (fun y : Fin (n + 1) → Bool => (∏ i : Fin (n + 1),
    (if xa i = y i then (1 + ρ) / 2 else (1 - ρ) / 2)) * f y)).trans ?_
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω' _
  rw [Fin.prod_univ_succ, hxa]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring


theorem bnt_qnormPow_cons_split {n : ℕ} (q : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    bnt_qnormPow q f
      = (∑ c : Bool, bnt_qnormPow q (fun ω' : Fin n → Bool => f (Fin.cons c ω'))) / 2 := by
  unfold bnt_qnormPow
  rw [bnt_uexp_cons_split (fun ω => |f ω| ^ q)]


theorem bnt_noiseOp_cons_false {n : ℕ} (ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ)
    (ω : Fin n → Bool) :
    bnt_noiseOp ρ f (Fin.cons false ω)
      = (1 + ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons false ω')) ω
        + (1 - ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons true ω')) ω := by
  rw [bnt_noiseOp_cons ρ f false ω, Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_true, if_false]; ring


theorem bnt_noiseOp_cons_true {n : ℕ} (ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ)
    (ω : Fin n → Bool) :
    bnt_noiseOp ρ f (Fin.cons true ω)
      = (1 - ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons false ω')) ω
        + (1 + ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons true ω')) ω := by
  rw [bnt_noiseOp_cons ρ f true ω, Fintype.sum_bool]
  simp only [Bool.true_eq_false, if_true, if_false]; ring


theorem bnt_qnorm_rpow_self {n : ℕ} {q : ℝ} (hq : q ≠ 0) (g : (Fin n → Bool) → ℝ) :
    bnt_qnorm q g ^ q = bnt_qnormPow q g := by
  unfold bnt_qnorm
  rw [← Real.rpow_mul (bnt_qnormPow_nonneg q g), one_div, inv_mul_cancel₀ hq, Real.rpow_one]


theorem bnt_qnorm_add_le {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (u v : (Fin n → Bool) → ℝ) :
    bnt_qnorm p (fun ω => u ω + v ω) ≤ bnt_qnorm p u + bnt_qnorm p v := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  unfold bnt_qnorm bnt_qnormPow bnt_uexp
  set N := Fintype.card (Fin n)
  have hc : (0 : ℝ) < 2 ^ N := by positivity
  rw [Real.div_rpow (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p)) (le_of_lt hc),
      Real.div_rpow (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p)) (le_of_lt hc),
      Real.div_rpow (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p)) (le_of_lt hc)]
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  calc (∑ ω : Fin n → Bool, |u ω + v ω| ^ p) ^ (1 / p)
      ≤ (∑ ω : Fin n → Bool, (|u ω| + |v ω|) ^ p) ^ (1 / p) := by
        apply Real.rpow_le_rpow (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p))
        · apply Finset.sum_le_sum; intro ω _
          exact Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (le_of_lt hp0)
        · positivity
    _ ≤ (∑ ω : Fin n → Bool, |u ω| ^ p) ^ (1 / p) + (∑ ω : Fin n → Bool, |v ω| ^ p) ^ (1 / p) :=
        Real.Lp_add_le_of_nonneg (s := Finset.univ) (f := fun ω => |u ω|) (g := fun ω => |v ω|) hp
          (fun ω _ => abs_nonneg _) (fun ω _ => abs_nonneg _)


theorem bnt_qnorm_const_mul {n : ℕ} {p : ℝ} (hp : 0 < p) (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    bnt_qnorm p (fun ω => c * f ω) = |c| * bnt_qnorm p f := by
  unfold bnt_qnorm bnt_qnormPow bnt_uexp
  have hcabs : ∀ ω : Fin n → Bool, |c * f ω| ^ p = |c| ^ p * |f ω| ^ p := by
    intro ω; rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  simp_rw [hcabs]
  rw [← Finset.mul_sum, mul_div_assoc,
      Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) p)
        (div_nonneg (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p))
          (by positivity))]
  congr 1
  rw [← Real.rpow_mul (abs_nonneg c), mul_one_div, div_self (ne_of_gt hp), Real.rpow_one]


end Probability
end StatMech
