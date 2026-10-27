import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[Jordan_outer_le_self](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {A: Set (EuclideanSpace' d)}
-- given
  (hA: IsElementary A) :
-- imply
  Jordan_outer_measure A ≤ hA.measure :=
-- proof
  Jordan_outer_le_self hA


-- created on 2026-10-22
