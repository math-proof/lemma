import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open ComplexSimpleFunction


/--
[ComplexSimpleFunction.add](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexSimpleFunction f)
  (hg: ComplexSimpleFunction g) :
-- imply
  ComplexSimpleFunction (f + g) :=
-- proof
  ComplexSimpleFunction.add hf hg


-- created on 2026-10-22
