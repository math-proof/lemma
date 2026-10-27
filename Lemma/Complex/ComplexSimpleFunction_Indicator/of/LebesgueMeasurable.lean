import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open ComplexSimpleFunction


/--
[ComplexSimpleFunction.indicator](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: LebesgueMeasurable E) :
-- imply
  ComplexSimpleFunction (Complex.indicator E) :=
-- proof
  ComplexSimpleFunction.indicator hE


-- created on 2026-10-22
