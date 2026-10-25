import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open IsElementary


/--
[IsElementary.empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  IsElementary (∅: Set (EuclideanSpace' d)) :=
-- proof
  IsElementary.empty d


-- created on 2026-10-22
