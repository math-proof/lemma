import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_707
open Mainstep


/--
[first_fixed](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {x:B}
-- given
  (hx: x.val ≠ 2) :
-- imply
  f (two_mul_sub_one_notin hx) x = x :=
-- proof
  Mainstep.first_fixed hx


-- created on 2026-10-22
