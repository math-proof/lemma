import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[A1_mem_redBlock1_of_red](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2}
  {i : Fin 2}
  {hAdj : G.Adj apex (A1 i)}
-- given
  (hRed : color (s(apex, A1 i)) = 1) :
-- imply
  A1 i ∈ redBlock1 color :=
-- proof
  PikhurkoN5.A1_mem_redBlock1_of_red color i hAdj hRed


-- created on 2026-10-22
