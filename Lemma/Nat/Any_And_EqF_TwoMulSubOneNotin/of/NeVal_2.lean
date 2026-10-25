import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_707.Part5
open Mainstep


/--
[second_fixed](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {x:B}
-- given
  (hx: x.val ≠ 2) :
-- imply
  ∃ b, b ≠ x ∧ f (two_mul_sub_one_notin hx) b = b :=
-- proof
  Mainstep.second_fixed hx


-- created on 2026-10-22
