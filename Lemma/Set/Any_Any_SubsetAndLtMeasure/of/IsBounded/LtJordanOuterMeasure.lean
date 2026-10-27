import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[le_Jordan_outer](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {m:ℝ}
-- given
  (hm: Jordan_outer_measure E < m)
  (hbound: Bornology.IsBounded E) :
-- imply
  ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, E ⊆ A ∧ hA.measure < m :=
-- proof
  le_Jordan_outer hm hbound


-- created on 2026-10-22
