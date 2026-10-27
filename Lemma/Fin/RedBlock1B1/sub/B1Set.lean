import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[redBlock1B1_subset_B1Set](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2} :
-- imply
  redBlock1B1 color ⊆ B1Set :=
-- proof
  PikhurkoN5.redBlock1B1_subset_B1Set color


-- created on 2026-10-22
