import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[degree_A1](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {i : Fin 2} :
-- imply
  G.degree (A1 i) = 7 :=
-- proof
  PikhurkoN5.degree_A1 i


-- created on 2026-10-22
