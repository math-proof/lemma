import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_7
open Chapter6.Sequence
open Real hiding rpow
open Chapter6
open Chapter6.Real


/--
[Real.ratPow_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_7.lean)
-/
@[path]
private lemma main
  {x q r : ℝ}
-- given
  (hx: x > 0) :
-- imply
  Chapter6.Real.rpow x (q+r) = Chapter6.Real.rpow x q * Chapter6.Real.rpow x r :=
-- proof
  Chapter6.Real.ratPow_add hx q r


-- created on 2026-10-22
