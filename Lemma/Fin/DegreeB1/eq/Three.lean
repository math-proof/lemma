import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[degree_B1](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {j : Fin 5} :
-- imply
  G.degree (B1 j) = 3 :=
-- proof
  PikhurkoN5.degree_B1 j


-- created on 2026-10-22
