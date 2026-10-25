import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open UnsignedSimpleFunction


/--
[UnsignedSimpleFunction.smul](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
  {a: EReal}
-- given
  (hf: UnsignedSimpleFunction f)
  (ha: a ≥ 0) :
-- imply
  UnsignedSimpleFunction (a • f) :=
-- proof
  UnsignedSimpleFunction.smul hf ha


-- created on 2026-10-22
