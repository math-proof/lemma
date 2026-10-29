/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Russo
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]


lemma bernoulliMeasure_real_singleton (p : NNReal) (hp : p ≤ 1) (b : Bool) :
    (bernoulliMeasure p hp).real {b} = if b then (p : ℝ) else 1 - p := by
  cases b with
  | true => rw [Measure.real, bernoulliMeasure_apply_true]; simp
  | false =>
      rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal, NNReal.coe_sub hp]
      simp

omit [Countable E] [DecidableEq E] in


lemma realSingleton_eq_configWeight [Fintype E] (p : NNReal) (hp : p ≤ 1)
    (ω : ConfigSpace E) :
    (bernoulliProductMeasure (E := E) p hp).real {ω} = configWeight (p : ℝ) ω := by
  rw [bernoulliProductMeasure.real_singleton]
  unfold configWeight edgeWeight
  exact Finset.prod_congr rfl (fun e _ => bernoulliMeasure_real_singleton p hp (ω e))

omit [Countable E] in


lemma finiteRealProb_eq_prob [Fintype E] (p : NNReal) (hp : p ≤ 1)
    (S : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real S = prob (p : ℝ) S := by
  rw [bernoulliProductMeasure.real_eq_sum]
  unfold prob
  exact Finset.sum_congr rfl
    (fun ω _ => by rw [realSingleton_eq_configWeight p hp ω])


end StatMech
