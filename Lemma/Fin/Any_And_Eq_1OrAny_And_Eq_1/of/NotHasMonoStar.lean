import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[exists_red_clique_neighbor](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2}
-- given
  (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
-- imply
  (∃ i : Fin 2, G.Adj apex (A1 i) ∧ color (s(apex, A1 i)) = 1) ∨
      (∃ i : Fin 3, G.Adj apex (A2 i) ∧ color (s(apex, A2 i)) = 1) :=
-- proof
  PikhurkoN5.exists_red_clique_neighbor color hNoBlueStar


-- created on 2026-10-22
