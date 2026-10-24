import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.abs_smul_unit](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
  {c: ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f)
  (hc: ‖c‖ = 1) :
-- imply
  (hf.smul c).abs.integ = hf.abs.integ :=
-- proof
  ComplexAbsolutelyIntegrable.abs_smul_unit hf c hc


-- created on 2026-10-22
