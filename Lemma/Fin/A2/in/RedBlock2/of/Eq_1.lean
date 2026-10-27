import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[A2_mem_redBlock2_of_red](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2}
  {i : Fin 3}
  {hAdj : G.Adj apex (A2 i)}
-- given
  (hRed : color (s(apex, A2 i)) = 1) :
-- imply
  A2 i ∈ redBlock2 color :=
-- proof
  PikhurkoN5.A2_mem_redBlock2_of_red color i hAdj hRed


-- created on 2026-10-22
