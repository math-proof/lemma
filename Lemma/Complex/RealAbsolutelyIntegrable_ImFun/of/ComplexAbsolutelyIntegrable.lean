import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.im](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f) :
-- imply
  RealAbsolutelyIntegrable (Complex.im_fun f) :=
-- proof
  ComplexAbsolutelyIntegrable.im f hf


-- created on 2026-10-22
