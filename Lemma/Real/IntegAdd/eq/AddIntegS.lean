import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.integ_add'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℝ}
-- given
  (hf: RealAbsolutelyIntegrable f)
  (hg: RealAbsolutelyIntegrable g) :
-- imply
  (hf.add hg).integ = hf.integ + hg.integ :=
-- proof
  RealAbsolutelyIntegrable.integ_add' hf hg


-- created on 2026-10-22
