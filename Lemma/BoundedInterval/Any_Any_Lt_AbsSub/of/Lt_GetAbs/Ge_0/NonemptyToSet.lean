import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Box
open Box.BoundedInterval


/--
[BoundedInterval.exists_points_with_diff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval}
  {t : ℝ}
-- given
  (h_nonempty : I.toSet.Nonempty)
  (ht_nonneg : 0 ≤ t)
  (ht : t < |I|ₗ) :
-- imply
  ∃ x ∈ I.toSet, ∃ y ∈ I.toSet, t < |x - y| :=
-- proof
  Box.BoundedInterval.exists_points_with_diff h_nonempty ht_nonneg ht


-- created on 2026-10-22
