import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_707.Part5
open Mainstep


/--
[diff_uniq](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {a b c d:B}
-- given
  (ha: a ≠ b)
  (hsub: a.val-b.val = c.val-d.val) :
-- imply
  a=c ∧ b=d :=
-- proof
  Mainstep.diff_uniq ha hsub


-- created on 2026-10-22
