import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_8
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[BoundedInterval.join_Ioc_Ioo'](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {a b c:ℝ}
-- given
  (hab: a ≤ b)
  (hbc: b < c) :
-- imply
  (Ioo a c).joins' (Ioc a b) (Ioo b c) :=
-- proof
  Chapter11.BoundedInterval.join_Ioc_Ioo' hab hbc


-- created on 2026-10-22
