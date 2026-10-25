import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open LebesgueMeasurable


/--
[LebesgueMeasurable.finite_inter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d n:ℕ}
  {E: Fin n → Set (EuclideanSpace' d)}
-- given
  (hE: ∀ i, LebesgueMeasurable (E i)) :
-- imply
  LebesgueMeasurable (⋂ i, E i) :=
-- proof
  LebesgueMeasurable.finite_inter hE


-- created on 2026-10-22
