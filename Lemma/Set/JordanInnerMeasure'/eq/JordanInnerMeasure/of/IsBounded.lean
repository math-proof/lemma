import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[Jordan_inner_measure'_eq_coe](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E) :
-- imply
  Jordan_inner_measure' E = ((Jordan_inner_measure E : ℝ) : EReal) :=
-- proof
  Jordan_inner_measure'_eq_coe hE


-- created on 2026-10-22
