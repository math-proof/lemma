import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.of_neg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f) :
-- imply
  ComplexAbsolutelyIntegrable (-f) :=
-- proof
  ComplexAbsolutelyIntegrable.of_neg hf


-- created on 2026-10-22
