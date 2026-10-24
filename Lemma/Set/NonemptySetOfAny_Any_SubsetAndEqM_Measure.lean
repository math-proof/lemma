import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2


/--
[Jordan_inner_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)} :
-- imply
  { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A,
        A ⊆ E ∧ m = hA.measure }.Nonempty :=
-- proof
  Jordan_inner_nonempty E


-- created on 2026-10-22
