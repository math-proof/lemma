import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_2
open LebesgueMeasurable


/--
[LebesgueMeasurable.countable_inter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: ℕ → Set (EuclideanSpace' d)}
-- given
  (hE: ∀ n, LebesgueMeasurable (E n)) :
-- imply
  LebesgueMeasurable (⋂ n, E n) :=
-- proof
  LebesgueMeasurable.countable_inter hE


-- created on 2026-10-22
