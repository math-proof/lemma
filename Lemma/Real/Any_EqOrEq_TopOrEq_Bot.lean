import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_2.Part2
open EReal


/--
[EReal.def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {x:EReal} :
-- imply
  (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ :=
-- proof
  EReal.def x


-- created on 2026-10-22
