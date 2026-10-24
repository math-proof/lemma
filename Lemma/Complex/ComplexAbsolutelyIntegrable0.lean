import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  ComplexAbsolutelyIntegrable (0 : EuclideanSpace' d → ℂ) :=
-- proof
  ComplexAbsolutelyIntegrable.zero


-- created on 2026-10-22
