import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[redBlock2B2_subset_B2Set](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2} :
-- imply
  redBlock2B2 color ⊆ B2Set :=
-- proof
  PikhurkoN5.redBlock2B2_subset_B2Set color


-- created on 2026-10-22
