import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_2
open EReal


/--
[EReal.sup_of_infty_mem](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {E: Set EReal}
-- given
  (hE: ⊤ ∈ E) :
-- imply
  sSup E = ⊤ :=
-- proof
  EReal.sup_of_infty_mem hE


-- created on 2026-10-22
