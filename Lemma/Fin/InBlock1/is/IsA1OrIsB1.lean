import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[inBlock1_iff](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {v : V} :
-- imply
  inBlock1 v ↔ (isA1 v ∨ isB1 v) :=
-- proof
  PikhurkoN5.inBlock1_iff v


-- created on 2026-10-22
