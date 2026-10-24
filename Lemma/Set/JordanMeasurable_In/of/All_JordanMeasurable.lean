import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_2
open JordanMeasurable


/--
[JordanMeasurable.union'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {S: Finset (Set (EuclideanSpace' d))}
-- given
  (hE: ∀ E ∈ S, JordanMeasurable E) :
-- imply
  JordanMeasurable (⋃ E ∈ S, E) :=
-- proof
  JordanMeasurable.union' hE


-- created on 2026-10-22
