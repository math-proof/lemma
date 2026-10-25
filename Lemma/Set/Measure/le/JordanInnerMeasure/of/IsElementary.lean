import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[le_Jordan_inner_self](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {A: Set (EuclideanSpace' d)}
-- given
  (hA: IsElementary A) :
-- imply
  hA.measure ≤ Jordan_inner_measure A :=
-- proof
  le_Jordan_inner_self hA


-- created on 2026-10-22
