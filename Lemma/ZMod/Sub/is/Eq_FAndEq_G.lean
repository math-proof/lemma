import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_707.Part5
open Mainstep


/--
[f_def'](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {a:ZMod N}
  {b c d:B}
-- given
  (ha: a ∉ B) :
-- imply
  a - b = c - d ↔ c = f ha b ∧ d = g ha b :=
-- proof
  Mainstep.f_def' ha b c d


-- created on 2026-10-22
