import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[redBlock2B2_card_le_5](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2} :
-- imply
  (redBlock2B2 color).card ≤ 5 :=
-- proof
  PikhurkoN5.redBlock2B2_card_le_5 color


-- created on 2026-10-22
