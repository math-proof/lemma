import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open IsElementary


/--
[IsElementary.contains_bounded](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E) :
-- imply
  ∃ A: Set (EuclideanSpace' d), IsElementary A ∧ E ⊆ A :=
-- proof
  IsElementary.contains_bounded hE


-- created on 2026-10-22
