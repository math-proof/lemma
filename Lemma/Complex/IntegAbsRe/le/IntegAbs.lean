import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.re_abs_integ_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f) :
-- imply
  hf.re.abs.integ ≤ hf.abs.integ :=
-- proof
  ComplexAbsolutelyIntegrable.re_abs_integ_le hf


-- created on 2026-10-22
