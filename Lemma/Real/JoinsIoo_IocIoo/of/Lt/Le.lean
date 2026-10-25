import Mathlib
import sympy.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.join_Ioc_Ioo](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {a b c:ℝ}
-- given
  (hab: a ≤ b)
  (hbc: b < c) :
-- imply
  (Ioo a c).joins (Ioc a b) (Ioo b c) :=
-- proof
  Chapter11.BoundedInterval.join_Ioc_Ioo hab hbc


-- created on 2026-10-22
