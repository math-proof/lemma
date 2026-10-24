import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Foundations.ProductMeasure
open MeasureTheory ProbabilityTheory StatMech StatMech.bernoulliProductMeasure


/--
[bernoulliMeasure_apply_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean)
-/
@[path]
private lemma bernoulliMeasure_apply_true_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  bernoulliMeasure p hp {true} = (p : ℝ≥0∞) := by
-- proof
  apply StatMech.bernoulliMeasure_apply_true p hp

/--
[bernoulliMeasure_apply_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean)
-/
@[path]
private lemma bernoulliMeasure_apply_false_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  bernoulliMeasure p hp {false} = ((1 - p : ℝ≥0) : ℝ≥0∞) := by
-- proof
  apply StatMech.bernoulliMeasure_apply_false p hp

/--
[apply_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean)
-/
@[path]
private lemma apply_singleton_eq
  {p : ℝ≥0}
  {hp : p ≤ 1}
  [Fintype E]
  {ω : ConfigSpace E} :
-- imply
  bernoulliProductMeasure (E := E) p hp {ω} = ∏ e, bernoulliMeasure p hp {ω e} := by
-- proof
  apply StatMech.bernoulliProductMeasure.apply_singleton ω

/--
[real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean)
-/
@[path]
private lemma real_singleton_eq
  {p : ℝ≥0}
  {hp : p ≤ 1}
  [Fintype E]
  {ω : ConfigSpace E} :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real {ω} = ∏ e, (bernoulliMeasure p hp).real {ω e} := by
-- proof
  apply StatMech.bernoulliProductMeasure.real_singleton ω

/--
[real_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean)
-/
@[path]
private lemma real_eq_sum_eq
  {p : ℝ≥0}
  {hp : p ≤ 1}
  [Fintype E]
  [DecidableEq E]
  {S : Set (ConfigSpace E)} :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real S = ∑ ω : ConfigSpace E, S.indicator (fun _ => (1 : ℝ)) ω * (bernoulliProductMeasure (E := E) p hp).real {ω} := by
-- proof
  apply StatMech.bernoulliProductMeasure.real_eq_sum S

/--
[real_singleton_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean)
-/
@[path]
private lemma real_singleton_nonneg_eq
  {p : ℝ≥0}
  {hp : p ≤ 1}
  {ω : ConfigSpace E} :
-- imply
  0 ≤ (bernoulliProductMeasure (E := E) p hp).real {ω} := by
-- proof
  apply StatMech.bernoulliProductMeasure.real_singleton_nonneg ω

/--
[sum_real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean)
-/
@[path]
private lemma sum_real_singleton_eq
  {p : ℝ≥0}
  {hp : p ≤ 1}
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∑ ω : ConfigSpace E, (bernoulliProductMeasure (E := E) p hp).real {ω} = 1 := by
-- proof
  apply StatMech.bernoulliProductMeasure.sum_real_singleton

/--
[real_singleton_logModular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean)
-/
@[path]
private lemma real_singleton_logModular_eq
  {p : ℝ≥0}
  {hp : p ≤ 1}
  [Fintype E]
  {a b : ConfigSpace E} :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real {a} * (bernoulliProductMeasure (E := E) p hp).real {b} = (bernoulliProductMeasure (E := E) p hp).real {a ⊔ b} * (bernoulliProductMeasure (E := E) p hp).real {a ⊓ b} := by
-- proof
  apply StatMech.bernoulliProductMeasure.real_singleton_logModular a b


-- created on 2026-10-23
