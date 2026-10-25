import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.norm_zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  (ComplexAbsolutelyIntegrable.zero (d:=d)).norm = 0 :=
-- proof
  ComplexAbsolutelyIntegrable.norm_zero


-- created on 2026-10-22
