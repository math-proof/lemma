import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_707.Part5
open Mainstep


/--
[two_mul_sub_one_notin](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {x:B}
-- given
  (hx: x.val ≠ 2) :
-- imply
  2 * (x.val - 1) ∉ B :=
-- proof
  Mainstep.two_mul_sub_one_notin hx


-- created on 2026-10-22
