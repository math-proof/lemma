import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open L1


/--
[L1.dist_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f)
  (hg: ComplexAbsolutelyIntegrable g) :
-- imply
  dist hf.toL1 hg.toL1 = (hf.sub hg).norm :=
-- proof
  L1.dist_eq f g hf hg


-- created on 2026-10-22
