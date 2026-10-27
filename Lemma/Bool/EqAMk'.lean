import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.mk'_a](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a b : ℝ}
  {lclosed uclosed : Bool} :
-- imply
  (mk' a b lclosed uclosed).a = a :=
-- proof
  BoundedInterval.mk'_a a b lclosed uclosed


-- created on 2026-10-22
