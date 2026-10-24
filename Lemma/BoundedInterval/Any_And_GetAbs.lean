import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise


/--
[BoundedInterval.length_of_translate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {c: ℝ} :
-- imply
  ∃ I' : BoundedInterval, I'.toSet = I.toSet + {c} ∧ |I'|ₗ = |I|ₗ :=
-- proof
  BoundedInterval.length_of_translate I c


-- created on 2026-10-22
