import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[midpoint_eq_a_add_half_length](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval}
-- given
  (h : I.a ≤ I.b) :
-- imply
  I.midpoint = I.a + |I|ₗ / 2 :=
-- proof
  BoundedInterval.midpoint_eq_a_add_half_length I h


-- created on 2026-10-22
