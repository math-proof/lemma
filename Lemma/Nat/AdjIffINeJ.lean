import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[adj_A1A1](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {i j} :
-- imply
  G.Adj (A1 i) (A1 j) ↔ i ≠ j :=
-- proof
  PikhurkoN5.adj_A1A1


-- created on 2026-10-22
