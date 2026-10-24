import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_3
open scoped Pointwise
open LebesgueMeasurable


/--
[LebesgueMeasurable.nonmeasurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  ∃ E : Set (EuclideanSpace' 1), E ⊆ Real.equiv_EuclideanSpace' '' (Set.Icc 0 1) ∧ ¬ LebesgueMeasurable E :=
-- proof
  LebesgueMeasurable.nonmeasurable


-- created on 2026-10-22
