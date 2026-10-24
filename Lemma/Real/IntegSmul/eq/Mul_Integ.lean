import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.integ_smul'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
  {c: ℝ}
-- given
  (hf: RealAbsolutelyIntegrable f) :
-- imply
  (hf.smul c).integ = c * hf.integ :=
-- proof
  RealAbsolutelyIntegrable.integ_smul' hf c


-- created on 2026-10-22
