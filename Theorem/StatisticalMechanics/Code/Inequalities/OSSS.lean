/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.Inequalities.OSSS.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


@[simp] lemma pt_self (b : Bool) : pt b b = 1 := by simp [pt]

lemma pt_apply (b c : Bool) : pt b c = if c = b then 1 else 0 := rfl


lemma weight_factor (ν : E → Bool → ℝ) (e : E) (ω : ConfigSpace E) :
    weight ν ω = ν e (ω e) * ∏ e' ∈ univ.erase e, ν e' (ω e') := by
  unfold weight
  rw [← Finset.prod_erase_mul univ _ (Finset.mem_univ e), mul_comm]


lemma restrict_update (ν : E → Bool → ℝ) (e : E) (ω : ConfigSpace E) (b : Bool) :
    (∏ e' ∈ univ.erase e, ν e' (Function.update ω e b e'))
      = ∏ e' ∈ univ.erase e, ν e' (ω e') := by
  apply Finset.prod_congr rfl
  intro e' he'
  rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]


lemma weight_cond (ν : E → Bool → ℝ) (e : E) (b : Bool) (ω : ConfigSpace E) :
    weight (Function.update ν e (pt b)) ω
      = pt b (ω e) * ∏ e' ∈ univ.erase e, ν e' (ω e') := by
  rw [weight_factor (Function.update ν e (pt b)) e ω, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro e' he'
  rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]


lemma expect_cond (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ) :
    expect ν g = ν e true * expect (Function.update ν e (pt true)) g
               + ν e false * expect (Function.update ν e (pt false)) g := by
  unfold expect
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  rw [weight_factor ν e ω, weight_cond ν e true ω, weight_cond ν e false ω]
  cases ω e <;>
    simp only [pt, Bool.false_eq_true, if_false, if_true, reduceCtorEq] <;> ring


lemma expect_add (ν : E → Bool → ℝ) (g h : ConfigSpace E → ℝ) :
    expect ν (fun ω => g ω + h ω) = expect ν g + expect ν h := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_sub (ν : E → Bool → ℝ) (g h : ConfigSpace E → ℝ) :
    expect ν (fun ω => g ω - h ω) = expect ν g - expect ν h := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_const_mul (ν : E → Bool → ℝ) (c : ℝ) (g : ConfigSpace E → ℝ) :
    expect ν (fun ω => c * g ω) = c * expect ν g := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_mono {ν : E → Bool → ℝ} (hν : IsProbWeight ν) {g h : ConfigSpace E → ℝ}
    (hgh : ∀ ω, g ω ≤ h ω) : expect ν g ≤ expect ν h := by
  unfold expect
  apply Finset.sum_le_sum
  intro ω _
  have hw : 0 ≤ weight ν ω := Finset.prod_nonneg (fun e _ => hν.nonneg e (ω e))
  exact mul_le_mul_of_nonneg_left (hgh ω) hw


lemma expect_one {ν : E → Bool → ℝ} (hν : IsProbWeight ν) :
    expect ν (fun _ => 1) = 1 := by
  unfold expect
  simp only [mul_one]
  unfold weight
  
  rw [← Fintype.prod_sum]
  rw [Finset.prod_eq_one]
  intro e _
  rw [Fintype.sum_bool, add_comm]
  exact hν.normalized e


end OSSS
end StatMech
