import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open JordanMeasurable


/--
[JordanMeasurable.measure_of_union'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {S: Finset (Set (EuclideanSpace' d))}
-- given
  (hE: ∀ E ∈ S, JordanMeasurable E) :
-- imply
  (JordanMeasurable.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure :=
-- proof
  JordanMeasurable.measure_of_union' hE


-- created on 2026-10-22
