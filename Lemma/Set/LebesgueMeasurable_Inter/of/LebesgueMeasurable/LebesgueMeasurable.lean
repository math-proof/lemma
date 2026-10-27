import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open LebesgueMeasurable


/--
[LebesgueMeasurable.inter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d :ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: LebesgueMeasurable E)
  (hF: LebesgueMeasurable F) :
-- imply
  LebesgueMeasurable (E ∩ F) :=
-- proof
  LebesgueMeasurable.inter hE hF


-- created on 2026-10-22
