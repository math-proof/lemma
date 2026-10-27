import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open IsElementary


/--
[IsElementary.jordanMeasurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E) :
-- imply
  JordanMeasurable E :=
-- proof
  IsElementary.jordanMeasurable hE


-- created on 2026-10-22
