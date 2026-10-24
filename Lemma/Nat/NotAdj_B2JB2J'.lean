import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[no_adj_B2B2](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {j j'} :
-- imply
  ¬ G.Adj (B2 j) (B2 j') :=
-- proof
  PikhurkoN5.no_adj_B2B2


-- created on 2026-10-22
