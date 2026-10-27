import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[fin2_eq_one_iff_ne_zero](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {a : Fin 2} :
-- imply
  (a = 1) ↔ a ≠ 0 :=
-- proof
  PikhurkoN5.fin2_eq_one_iff_ne_zero a


-- created on 2026-10-22
