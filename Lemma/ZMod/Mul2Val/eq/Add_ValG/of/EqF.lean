import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_707.Part5
open Mainstep


/--
[f_fixed](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {a:ZMod N}
  {ha: a ∉ B}
  {b:B}
-- given
  (hb: f ha b = b) :
-- imply
  2 * b.val = a + (g ha b).val :=
-- proof
  Mainstep.f_fixed hb


-- created on 2026-10-22
