/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.Inequalities.OSSS.Part5
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


open DecisionTree

lemma expect_cond_forces (ν : E → Bool → ℝ) (e : E) (b : Bool) (h : ConfigSpace E → ℝ) :
    expect (Function.update ν e (pt b)) h
      = expect (Function.update ν e (pt b)) (fun ω => h (Function.update ω e b)) := by
  unfold expect
  apply Finset.sum_congr rfl
  intro ω _
  rw [weight_cond ν e b ω]
  simp only []
  by_cases hb : ω e = b
  · have : Function.update ω e b = ω := by
      funext e'
      by_cases he : e' = e
      · subst he; simp [hb]
      · rw [Function.update_of_ne he]
    rw [this]
  · have h0 : pt b (ω e) = 0 := by simp [pt, hb]
    rw [h0]; ring

lemma reveal_root (hν : IsProbWeight ν) (e : E) (t f : DecisionTree E) :
    reveal ν (.node e t f) e = 1 := by
  unfold reveal
  have : (fun ω => if e ∈ (DecisionTree.node e t f).queried ω then (1:ℝ) else 0)
       = (fun _ => (1:ℝ)) := by
    funext ω
    rw [if_pos]; unfold DecisionTree.queried; exact Finset.mem_insert_self e _
  rw [this, expect_one hν]

omit [Fintype E] in
lemma mem_queried_node_iff (e i : E) (hi : i ≠ e) (t f : DecisionTree E)
    (ω : ConfigSpace E) (b : Bool) (h : ω e = b) :
    (i ∈ (DecisionTree.node e t f).queried ω) ↔ (i ∈ (if b then t else f).queried ω) := by
  conv_lhs => unfold DecisionTree.queried
  rw [h, Finset.mem_insert]
  cases b <;> simp [hi]

lemma expect_indQ_node_cond (ν : E → Bool → ℝ) (e i : E) (hi : i ≠ e) (b : Bool)
    (t f : DecisionTree E) :
    expect (Function.update ν e (pt b))
        (fun ω => if i ∈ (DecisionTree.node e t f).queried ω then (1:ℝ) else 0)
      = expect (Function.update ν e (pt b))
        (fun ω => if i ∈ (if b then t else f).queried ω then (1:ℝ) else 0) := by
  rw [expect_cond_forces ν e b, expect_cond_forces ν e b
        (fun ω => if i ∈ (if b then t else f).queried ω then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  congr 1
  have hωe : (Function.update ω e b) e = b := Function.update_self e b ω
  exact if_congr (mem_queried_node_iff e i hi t f _ b hωe) rfl rfl

lemma reveal_node_ne (ν : E → Bool → ℝ) (e i : E) (hi : i ≠ e) (t f : DecisionTree E) :
    reveal ν (.node e t f) i
      = ν e true * reveal (Function.update ν e (pt true)) t i
      + ν e false * reveal (Function.update ν e (pt false)) f i := by
  unfold reveal
  rw [expect_cond ν e]
  rw [expect_indQ_node_cond ν e i hi true t f, expect_indQ_node_cond ν e i hi false t f]
  simp only [if_true, Bool.false_eq_true, if_false]


lemma infl_cond (ν : E → Bool → ℝ) (e : E) (h : ConfigSpace E → ℝ) (i : E) :
    infl ν h i = ν e true * infl (Function.update ν e (pt true)) h i
               + ν e false * infl (Function.update ν e (pt false)) h i := by
  unfold infl
  exact expect_cond ν e _


lemma infl_condMean_self (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ) :
    infl ν (condMean ν e g) e = 0 := by
  unfold infl
  have : (fun ω => |condMean ν e g (setOpen e ω) - condMean ν e g (setClosed e ω)|)
       = (fun _ => (0:ℝ)) := by
    funext ω
    rw [condMean_setOpen, condMean_setClosed, sub_self, abs_zero]
  rw [this]
  unfold expect; simp


end OSSS
end StatMech
