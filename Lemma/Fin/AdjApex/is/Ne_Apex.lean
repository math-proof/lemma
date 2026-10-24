import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[adj_apex_left](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {v : V} :
-- imply
  G.Adj V.apex v ↔ v ≠ V.apex :=
-- proof
  PikhurkoN5.adj_apex_left


-- created on 2026-10-22
