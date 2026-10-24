import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.union'_empty_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  (⋃ E ∈ (∅ : Finset (Set (EuclideanSpace' d))), E) = ∅ :=
-- proof
  IsElementary.union'_empty_eq


-- created on 2026-10-22
