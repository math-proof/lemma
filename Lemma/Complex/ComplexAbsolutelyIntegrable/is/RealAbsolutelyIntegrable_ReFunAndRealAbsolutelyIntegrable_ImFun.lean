import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ} :
-- imply
  ComplexAbsolutelyIntegrable f ↔ RealAbsolutelyIntegrable (Complex.re_fun f) ∧ RealAbsolutelyIntegrable (Complex.im_fun f) :=
-- proof
  ComplexAbsolutelyIntegrable.iff f


-- created on 2026-10-22
