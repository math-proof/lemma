import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[no_cross_blocks_A1B2](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {i j} :
-- imply
  ¬ G.Adj (A1 i) (B2 j) :=
-- proof
  PikhurkoN5.no_cross_blocks_A1B2


-- created on 2026-10-22
