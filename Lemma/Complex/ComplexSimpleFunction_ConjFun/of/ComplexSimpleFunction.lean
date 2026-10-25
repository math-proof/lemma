import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open ComplexSimpleFunction


/--
[ComplexSimpleFunction.conj](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexSimpleFunction f) :
-- imply
  ComplexSimpleFunction (Complex.conj_fun f) :=
-- proof
  ComplexSimpleFunction.conj hf


-- created on 2026-10-22
