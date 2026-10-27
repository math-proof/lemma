import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[redBlock2_eq_union](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2} :
-- imply
  redBlock2 color =
    redBlock2A2 color ∪ redBlock2B2 color :=
-- proof
  PikhurkoN5.redBlock2_eq_union color


-- created on 2026-10-22
