/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Revealment.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace Revealment

open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] in


lemma card_queried_le_depth (T : DecisionTree E) (ω : ConfigSpace E) :
    (T.queried ω).card ≤ depth T := by
  induction T generalizing ω with
  | leaf b =>
      simp only [DecisionTree.queried, depth, Finset.card_empty, le_refl]
  | node e t f IHt IHf =>
      simp only [DecisionTree.queried, depth]
      refine le_trans (Finset.card_insert_le _ _) ?_
      have hsub : (if ω e then t.queried ω else f.queried ω).card ≤ max (depth t) (depth f) := by
        by_cases he : ω e
        · simp only [he, if_true]; exact le_trans (IHt ω) (le_max_left _ _)
        · simp only [he, Bool.false_eq_true, if_false]; exact le_trans (IHf ω) (le_max_right _ _)
      omega


theorem sum_revealment_le_depth {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (T : DecisionTree E) :
    ∑ e, revealment ν T e ≤ (depth T : ℝ) := by
  rw [sum_revealment_eq_expect_card]
  rw [show ((depth T : ℝ)) = expect ν (fun _ => (depth T : ℝ)) from ?_]
  · apply expect_mono hν
    intro ω
    exact_mod_cast card_queried_le_depth T ω
  · rw [show (fun _ : ConfigSpace E => (depth T : ℝ))
          = (fun ω => (depth T : ℝ) * (fun _ => (1 : ℝ)) ω) from by funext; simp]
    rw [expect_const_mul, expect_one hν, mul_one]


theorem revealment_le_of_queried_imp {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (T : DecisionTree E) (e : E) (P : ConfigSpace E → Prop) [DecidablePred P]
    (h : ∀ ω, e ∈ T.queried ω → P ω) :
    revealment ν T e ≤ expect ν (fun ω => if P ω then (1 : ℝ) else 0) := by
  rw [revealment_eq_prob_queried]
  apply expect_mono hν
  intro ω
  by_cases hq : e ∈ T.queried ω
  · rw [if_pos hq, if_pos (h ω hq)]
  · rw [if_neg hq]; split <;> norm_num


theorem revealment_le_of_queried_imp_or {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (T : DecisionTree E) (e : E) (P Q : ConfigSpace E → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ ω, e ∈ T.queried ω → P ω ∨ Q ω) :
    revealment ν T e
      ≤ expect ν (fun ω => if P ω then (1 : ℝ) else 0)
        + expect ν (fun ω => if Q ω then (1 : ℝ) else 0) := by
  have hbound : revealment ν T e
      ≤ expect ν (fun ω => (if P ω then (1 : ℝ) else 0) + (if Q ω then (1 : ℝ) else 0)) := by
    rw [revealment_eq_prob_queried]
    apply expect_mono hν
    intro ω
    by_cases hq : e ∈ T.queried ω
    · rw [if_pos hq]
      rcases h ω hq with hP | hQ
      · rw [if_pos hP]
        have : (0 : ℝ) ≤ if Q ω then (1 : ℝ) else 0 := by split <;> norm_num
        linarith
      · rw [if_pos hQ]
        have : (0 : ℝ) ≤ if P ω then (1 : ℝ) else 0 := by split <;> norm_num
        linarith
    · rw [if_neg hq]
      have h1 : (0 : ℝ) ≤ if P ω then (1 : ℝ) else 0 := by split <;> norm_num
      have h2 : (0 : ℝ) ≤ if Q ω then (1 : ℝ) else 0 := by split <;> norm_num
      linarith
  rwa [expect_add ν (fun ω => if P ω then (1 : ℝ) else 0)
        (fun ω => if Q ω then (1 : ℝ) else 0)] at hbound

end Revealment
end OSSS
end StatMech
