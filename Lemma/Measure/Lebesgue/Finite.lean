import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Measure.Lebesgue.Finite
open Set
open scoped ENNReal
open MeasureTheory


/--
[exists_gt_not_mem_of_volume_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/Finite.lean)
-/
@[path]
private lemma exists_gt_not_mem_of_volume_lt_top_eq
  {E : Set ℝ}
  {X : ℝ}
-- given
  (hE : volume E < ∞) :
-- imply
  ∃ x : ℝ, X < x ∧ x ∉ E := by
-- proof
  apply MeasureTheory.exists_gt_not_mem_of_volume_lt_top E hE X


-- created on 2026-10-20
