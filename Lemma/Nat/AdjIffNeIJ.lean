import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[adj_A2A2](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {i j} :
-- imply
  G.Adj (A2 i) (A2 j) ↔ i ≠ j :=
-- proof
  PikhurkoN5.adj_A2A2


-- created on 2026-10-22
