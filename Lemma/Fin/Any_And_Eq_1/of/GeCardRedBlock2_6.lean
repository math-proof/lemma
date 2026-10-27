import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[exists_red_A2_of_block2_ge6](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2}
-- given
  (h0 : 6 ≤ (redBlock2 color).card) :
-- imply
  ∃ i : Fin 3, G.Adj apex (A2 i) ∧ color (s(apex, A2 i)) = 1 :=
-- proof
  PikhurkoN5.exists_red_A2_of_block2_ge6 color h0


-- created on 2026-10-22
