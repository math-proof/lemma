import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_1
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.join_Icc_Ioc](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {a b c:ℝ}
-- given
  (hab: a ≤ b)
  (hbc: b ≤ c) :
-- imply
  (Icc a c).joins (Icc a b) (Ioc b c) :=
-- proof
  Chapter11.BoundedInterval.join_Icc_Ioc hab hbc


-- created on 2026-10-22
