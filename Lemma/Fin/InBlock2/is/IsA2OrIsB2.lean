import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[inBlock2_iff](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {v : V} :
-- imply
  inBlock2 v ↔ (isA2 v ∨ isB2 v) :=
-- proof
  PikhurkoN5.inBlock2_iff v


-- created on 2026-10-22
