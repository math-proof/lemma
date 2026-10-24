import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2


/--
[Jordan_outer_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E A: Set (EuclideanSpace' d)}
-- given
  (hA: IsElementary A)
  (hAE: E ⊆ A) :
-- imply
  Jordan_outer_measure E ≤ hA.measure :=
-- proof
  Jordan_outer_le hA hAE


-- created on 2026-10-22
