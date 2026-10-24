import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[redA1_redB1_disjoint](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2} :
-- imply
  Disjoint (redBlock1A1 color) (redBlock1B1 color) :=
-- proof
  PikhurkoN5.redA1_redB1_disjoint color


-- created on 2026-10-22
