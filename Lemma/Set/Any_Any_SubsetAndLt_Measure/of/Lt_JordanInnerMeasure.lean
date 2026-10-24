import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2


/--
[Jordan_inner_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {m:ℝ}
-- given
  (hm: m < Jordan_inner_measure E) :
-- imply
  ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, A ⊆ E ∧ m < hA.measure :=
-- proof
  Jordan_inner_le hm


-- created on 2026-10-22
