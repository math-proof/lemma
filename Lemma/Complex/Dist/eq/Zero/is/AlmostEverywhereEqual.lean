import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open L1


/--
[L1.dist_eq_zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f)
  (hg: ComplexAbsolutelyIntegrable g) :
-- imply
  dist hf.toL1 hg.toL1 = 0 ↔ AlmostEverywhereEqual f g :=
-- proof
  L1.dist_eq_zero f g hf hg


-- created on 2026-10-22
