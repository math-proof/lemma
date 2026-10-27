import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open RealSimpleFunction


/--
[RealSimpleFunction.indicator](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: LebesgueMeasurable E) :
-- imply
  RealSimpleFunction E.indicator' :=
-- proof
  RealSimpleFunction.indicator hE


-- created on 2026-10-22
