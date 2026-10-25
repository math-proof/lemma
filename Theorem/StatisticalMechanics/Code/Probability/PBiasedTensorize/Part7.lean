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
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part7
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_noiseOp_l2sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (f : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (ptn_noiseOp p ρ f ω) ^ 2)
      = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2 := by
  unfold ptn_noiseOp
  have hT : Set.InjOn (fun S : Finset ι => S) ↑(univ : Finset (Finset ι)) :=
    fun _ _ _ _ h => h
  rw [ptn_expect_sum_pchar_sq hp0 hp1 univ (fun S => ρ ^ S.card * ptn_coeff p f S)
      (fun S => S) hT]
  apply Finset.sum_congr rfl; intro S _; ring


theorem ptn_qnormPow2_eq_expect_sq {p : ℝ} (f : ConfigSpace ι → ℝ) :
    ptn_qnormPow p 2 f = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2) := by
  unfold ptn_qnormPow
  congr 1; funext ω
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]


theorem ptn_qnorm2_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ConfigSpace ι → ℝ) :
    (ptn_qnorm p 2 f) ^ 2 = ptn_qnormPow p 2 f := by
  rw [show (ptn_qnorm p 2 f) ^ 2 = (ptn_qnorm p 2 f) ^ (2 : ℝ) from by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  exact ptn_qnorm_rpow_self hp0 hp1 (by norm_num) f


theorem ptn_sum_cons_split {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin (n + 1) → Bool) → M) :
    (∑ y : Fin (n + 1) → Bool, F y)
      = ∑ c : Bool, ∑ ω' : Fin n → Bool, F (Fin.cons c ω') := by
  rw [← Fintype.sum_prod_type (fun q : Bool × (Fin n → Bool) => F (Fin.cons q.1 q.2))]
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool))
    (fun q => F (Fin.cons q.1 q.2)) F (fun _ => rfl)).symm


theorem ptn_expect_cons_split {n : ℕ} (p : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) f
      = (1 - p) * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => f (Fin.cons false ω'))
        + p * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => f (Fin.cons true ω')) := by
  unfold OSSS.expect
  rw [ptn_sum_cons_split (fun y => OSSS.weight (OSSS.bernoulliWeight p) y * f y), Fintype.sum_bool]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [show (∑ x : Fin n → Bool, (1 - p) * (OSSS.weight (OSSS.bernoulliWeight p) x * f (Fin.cons false x)))
        + ∑ x : Fin n → Bool, p * (OSSS.weight (OSSS.bernoulliWeight p) x * f (Fin.cons true x))
      = ∑ x : Fin n → Bool, ((1 - p) * (OSSS.weight (OSSS.bernoulliWeight p) x * f (Fin.cons false x))
          + p * (OSSS.weight (OSSS.bernoulliWeight p) x * f (Fin.cons true x)))
      from (Finset.sum_add_distrib).symm]
  rw [show (∑ ω' : Fin n → Bool, OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons true ω') * f (Fin.cons true ω'))
        + ∑ ω' : Fin n → Bool, OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons false ω') * f (Fin.cons false ω')
      = ∑ ω' : Fin n → Bool, (OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons true ω') * f (Fin.cons true ω')
          + OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons false ω') * f (Fin.cons false ω'))
      from (Finset.sum_add_distrib).symm]
  apply Finset.sum_congr rfl
  intro ω' _
  
  have hwc : ∀ c : Bool, OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons c ω')
      = OSSS.bernoulliWeight p (0 : Fin (n+1)) c * OSSS.weight (OSSS.bernoulliWeight p) ω' := by
    intro c
    unfold OSSS.weight
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, OSSS.bernoulliWeight]
  rw [hwc false, hwc true]
  unfold OSSS.bernoulliWeight
  simp only [Bool.false_eq_true, if_false, if_true]
  ring


end StatMech.Probability
