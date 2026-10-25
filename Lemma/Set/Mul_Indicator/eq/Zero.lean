import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[indicator_mul_not_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {E : Set (EuclideanSpace' d)}
  {c : EReal}
  {x : EuclideanSpace' d}
-- given
  (h : x ∉ E) :
-- imply
  c * (EReal.indicator E x) = 0 :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.indicator_mul_not_mem E c x h


-- created on 2026-10-22
