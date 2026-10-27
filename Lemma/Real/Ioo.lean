import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.set_Ioo](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {a b:ℝ} :
-- imply
  (Ioo a b : Set ℝ) = .Ioo a b :=
-- proof
  BoundedInterval.set_Ioo a b


-- created on 2026-10-22
