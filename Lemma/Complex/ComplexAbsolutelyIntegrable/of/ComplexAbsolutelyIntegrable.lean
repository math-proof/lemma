import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.smul](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
  {c:ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f) :
-- imply
  ComplexAbsolutelyIntegrable (c • f) :=
-- proof
  ComplexAbsolutelyIntegrable.smul hf c


-- created on 2026-10-22
