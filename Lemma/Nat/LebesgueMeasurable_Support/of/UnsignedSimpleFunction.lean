import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open UnsignedSimpleFunction


/--
[UnsignedSimpleFunction.support_measurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
-- given
  (hf: UnsignedSimpleFunction f) :
-- imply
  LebesgueMeasurable (Support f) :=
-- proof
  UnsignedSimpleFunction.support_measurable hf


-- created on 2026-10-22
