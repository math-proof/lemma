import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[redBlock2_card_eq_sum](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2} :
-- imply
  (redBlock2 color).card
    = (redBlock2A2 color).card + (redBlock2B2 color).card :=
-- proof
  PikhurkoN5.redBlock2_card_eq_sum color


-- created on 2026-10-22
