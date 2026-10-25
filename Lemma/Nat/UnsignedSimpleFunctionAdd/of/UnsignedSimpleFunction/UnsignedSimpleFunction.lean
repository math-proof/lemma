import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open UnsignedSimpleFunction


/--
[UnsignedSimpleFunction.add](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → EReal}
-- given
  (hf: UnsignedSimpleFunction f)
  (hg: UnsignedSimpleFunction g) :
-- imply
  UnsignedSimpleFunction (f + g) :=
-- proof
  UnsignedSimpleFunction.add hf hg


-- created on 2026-10-22
