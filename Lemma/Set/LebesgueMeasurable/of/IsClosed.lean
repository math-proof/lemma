import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open IsClosed


/--
[IsClosed.measurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: IsClosed E) :
-- imply
  LebesgueMeasurable E :=
-- proof
  IsClosed.measurable hE


-- created on 2026-10-22
