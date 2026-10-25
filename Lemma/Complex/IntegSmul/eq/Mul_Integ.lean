import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.integ_smul](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
  {c: ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f) :
-- imply
  (hf.smul c).integ = c * hf.integ :=
-- proof
  ComplexAbsolutelyIntegrable.integ_smul hf c


-- created on 2026-10-22
