import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_6
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.ratPow_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_6.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real}
  {a:ℤ}
  {b:ℕ}
-- given
  (hx: x > 0)
  (hb: b > 0) :
-- imply
  x^(a/b:ℚ) = (x.root b)^a :=
-- proof
  Chapter5.Real.ratPow_def hx a hb


-- created on 2026-10-22
