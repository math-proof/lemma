/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*}


namespace bernoulliProductMeasure

variable {p : ℝ≥0} {hp : p ≤ 1}


theorem apply_singleton [Fintype E] (ω : ConfigSpace E) :
    bernoulliProductMeasure (E := E) p hp {ω} = ∏ e, bernoulliMeasure p hp {ω e} := by
  unfold bernoulliProductMeasure
  rw [Measure.infinitePi_singleton_of_fintype]


theorem real_singleton [Fintype E] (ω : ConfigSpace E) :
    (bernoulliProductMeasure (E := E) p hp).real {ω}
      = ∏ e, (bernoulliMeasure p hp).real {ω e} := by
  rw [Measure.real, apply_singleton, ENNReal.toReal_prod]
  rfl


theorem real_eq_sum [Fintype E] [DecidableEq E] (S : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real S
      = ∑ ω : ConfigSpace E,
          S.indicator (fun _ => (1 : ℝ)) ω * (bernoulliProductMeasure (E := E) p hp).real {ω} := by
  classical
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  have key : μ.real S = ∑ ω ∈ Finset.univ.filter (· ∈ S), μ.real {ω} := by
    have h1 : μ S = ∑ ω ∈ Finset.univ.filter (· ∈ S), μ {ω} := by
      rw [sum_measure_singleton]; congr 1; ext x; simp
    rw [Measure.real, h1, ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
    rfl
  rw [key, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases h : ω ∈ S
  · rw [if_pos h, Set.indicator_of_mem h]; ring
  · rw [if_neg h, Set.indicator_of_notMem h]; ring


theorem real_singleton_nonneg (ω : ConfigSpace E) :
    0 ≤ (bernoulliProductMeasure (E := E) p hp).real {ω} :=
  ENNReal.toReal_nonneg


theorem sum_real_singleton [Fintype E] [DecidableEq E] :
    ∑ ω : ConfigSpace E, (bernoulliProductMeasure (E := E) p hp).real {ω} = 1 := by
  classical
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  have h : ∑ ω : ConfigSpace E, μ {ω} = μ Set.univ := by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
  have h2 : ∑ ω : ConfigSpace E, μ.real {ω} = (μ Set.univ).toReal := by
    simp only [Measure.real]
    rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top _ _), h]
  rw [h2, measure_univ, ENNReal.toReal_one]

set_option linter.unusedFintypeInType false in


theorem real_singleton_logModular [Fintype E] (a b : ConfigSpace E) :
    (bernoulliProductMeasure (E := E) p hp).real {a}
        * (bernoulliProductMeasure (E := E) p hp).real {b}
      = (bernoulliProductMeasure (E := E) p hp).real {a ⊔ b}
        * (bernoulliProductMeasure (E := E) p hp).real {a ⊓ b} := by
  have coord : ∀ (φ : Bool → ℝ) (x y : Bool), φ x * φ y = φ (x ⊔ y) * φ (x ⊓ y) := by
    intro φ x y
    rcases le_total x y with h | h
    · rw [sup_eq_right.mpr h, inf_eq_left.mpr h]; ring
    · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]
  simp_rw [real_singleton]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  simp only [Pi.sup_apply, Pi.inf_apply]
  exact coord (fun b => (bernoulliMeasure p hp).real {b}) (a e) (b e)

end bernoulliProductMeasure
end StatMech
