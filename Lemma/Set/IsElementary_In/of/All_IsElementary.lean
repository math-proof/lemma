import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open IsElementary


/--
[IsElementary.union'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {S: Finset (Set (EuclideanSpace' d))}
-- given
  (hE: ∀ E ∈ S, IsElementary E) :
-- imply
  IsElementary (⋃ E ∈ S, E) :=
-- proof
  IsElementary.union' hE


-- created on 2026-10-22
