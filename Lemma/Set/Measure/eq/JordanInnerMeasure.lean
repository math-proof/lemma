import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open JordanMeasurable


/--
[JordanMeasurable.eq_inner](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: JordanMeasurable E) :
-- imply
  hE.measure = Jordan_inner_measure E :=
-- proof
  JordanMeasurable.eq_inner hE


-- created on 2026-10-22
