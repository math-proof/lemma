import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open LebesgueMeasurable


/--
[LebesgueMeasurable.finset_inter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  [DecidableEq α]
  {d : ℕ}
  {E : α → Set (EuclideanSpace' d)}
  {S : Finset α}
-- given
  (hE : ∀ i ∈ S, LebesgueMeasurable (E i)) :
-- imply
  LebesgueMeasurable (⋂ i ∈ S, E i) :=
-- proof
  LebesgueMeasurable.finset_inter hE


-- created on 2026-10-22
