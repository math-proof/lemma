import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[degree_A2](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {i : Fin 3} :
-- imply
  G.degree (A2 i) = 8 :=
-- proof
  PikhurkoN5.degree_A2 i


-- created on 2026-10-22
