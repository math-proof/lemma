import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_707.Part5
open Mainstep


/--
[b_neq](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {x:B}
-- given
  (hx: x.val ≠ 2) :
-- imply
  b x ≠ x :=
-- proof
  Mainstep.b_neq hx


-- created on 2026-10-22
