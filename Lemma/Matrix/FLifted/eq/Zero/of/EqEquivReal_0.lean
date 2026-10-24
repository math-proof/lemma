import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Remark_1_3_10


/--
[f_lifted_zero_at_zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : EuclideanSpace' 1}
-- given
  (hx : EuclideanSpace'.equiv_Real x = 0) :
-- imply
  f_lifted x = 0 :=
-- proof
  Remark_1_3_10.f_lifted_zero_at_zero x hx


-- created on 2026-10-22
