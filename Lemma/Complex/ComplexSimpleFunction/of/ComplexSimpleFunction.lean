import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open ComplexSimpleFunction


/--
[ComplexSimpleFunction.smul](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
  {a: ℂ}
-- given
  (hf: ComplexSimpleFunction f) :
-- imply
  ComplexSimpleFunction (a • f) :=
-- proof
  ComplexSimpleFunction.smul hf a


-- created on 2026-10-22
