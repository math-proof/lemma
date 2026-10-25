/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.Inequalities.OSSS.Part7
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


open DecisionTree

omit [Fintype E] [DecidableEq E] in

lemma bernoulliWeight_isProbWeight {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbWeight (E := E) (bernoulliWeight p) := by
  constructor
  · intro e b; unfold bernoulliWeight; cases b <;> simp <;> linarith
  · intro e; unfold bernoulliWeight; simp


theorem osss_bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : DecisionTree E) (g : ConfigSpace E → ℝ) :
    cov (bernoulliWeight p) T.evalR g
      ≤ ∑ i, reveal (bernoulliWeight p) T i * infl (bernoulliWeight p) g i :=
  osss_cov T (bernoulliWeight p) (bernoulliWeight_isProbWeight hp0 hp1) g


omit [Fintype E] in


lemma abs_indicator_diff_eq_pivotal (A : Set (ConfigSpace E)) (e : E) (ω : ConfigSpace E) :
    |A.indicator (fun _ => (1:ℝ)) (setOpen e ω) - A.indicator (fun _ => (1:ℝ)) (setClosed e ω)|
      = {ω | IsPivotal e A ω}.indicator (fun _ => (1:ℝ)) ω := by
  by_cases hp : IsPivotal e A ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | IsPivotal e A ω} from hp)]
    unfold IsPivotal at hp
    by_cases hO : setOpen e ω ∈ A <;> by_cases hC : setClosed e ω ∈ A <;>
      simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | IsPivotal e A ω} from hp)]
    unfold IsPivotal at hp
    by_cases hO : setOpen e ω ∈ A <;> by_cases hC : setClosed e ω ∈ A <;>
      simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]


theorem infl_indicator_eq_pivotal (ν : E → Bool → ℝ) (A : Set (ConfigSpace E)) (e : E) :
    infl ν (A.indicator (fun _ => (1:ℝ))) e
      = expect ν ({ω | IsPivotal e A ω}.indicator (fun _ => (1:ℝ))) := by
  unfold infl
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  rw [abs_indicator_diff_eq_pivotal]

end OSSS
end StatMech
