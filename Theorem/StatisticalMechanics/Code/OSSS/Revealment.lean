/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Revealment
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace Revealment

open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


@[simp] lemma revealment_eq_reveal (ν : E → Bool → ℝ) (T : DecisionTree E) (e : E) :
    revealment ν T e = reveal ν T e := rfl


lemma revealment_eq_prob_queried (ν : E → Bool → ℝ) (T : DecisionTree E) (e : E) :
    revealment ν T e = expect ν (fun ω => if e ∈ T.queried ω then (1 : ℝ) else 0) := rfl


lemma revealment_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (T : DecisionTree E)
    (e : E) : 0 ≤ revealment ν T e :=
  reveal_nonneg hν T e


lemma revealment_le_one {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (T : DecisionTree E)
    (e : E) : revealment ν T e ≤ 1 := by
  rw [revealment_eq_prob_queried]
  calc expect ν (fun ω => if e ∈ T.queried ω then (1 : ℝ) else 0)
      ≤ expect ν (fun _ => (1 : ℝ)) := by
        apply expect_mono hν; intro ω; split <;> norm_num
    _ = 1 := expect_one hν


lemma sum_indicator_mem_card (S : Finset E) :
    ∑ e, (if e ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]


theorem sum_revealment_eq_expect_card (ν : E → Bool → ℝ) (T : DecisionTree E) :
    ∑ e, revealment ν T e = expect ν (fun ω => ((T.queried ω).card : ℝ)) := by
  simp only [revealment_eq_prob_queried, expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  
  rw [← Finset.mul_sum, sum_indicator_mem_card]


end Revealment
end OSSS
end StatMech
