import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[le_Jordan_inner](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E A: Set (EuclideanSpace' d)}
-- given
  (hA: IsElementary A)
  (hAE: A ⊆ E)
  (hE: Bornology.IsBounded E) :
-- imply
  hA.measure ≤ Jordan_inner_measure E :=
-- proof
  le_Jordan_inner hA hAE hE


-- created on 2026-10-22
