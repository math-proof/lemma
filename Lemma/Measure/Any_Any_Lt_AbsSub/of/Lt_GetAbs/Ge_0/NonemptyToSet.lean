import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box
open Box.BoundedInterval
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
