import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_2
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
