import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_2
open LebesgueMeasurable


/--
[LebesgueMeasurable.union](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d :ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: LebesgueMeasurable E)
  (hF: LebesgueMeasurable F) :
-- imply
  LebesgueMeasurable (E ∪ F) :=
-- proof
  LebesgueMeasurable.union hE hF


-- created on 2026-10-22
