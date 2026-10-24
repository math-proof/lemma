import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open scoped Classical
open UnsignedSimpleFunction.IntegralWellDef


/--
[indicator_mul_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {E : Set (EuclideanSpace' d)}
  {c : EReal}
  {x : EuclideanSpace' d}
-- given
  (h : x ∈ E) :
-- imply
  c * (EReal.indicator E x) = c :=
-- proof
  UnsignedSimpleFunction.IntegralWellDef.indicator_mul_mem E c x h


-- created on 2026-10-22
