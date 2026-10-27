import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_4_4


/--
[exists_between_rat](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_4.lean)
-/
@[path]
private lemma main
  {x y:ℚ}
-- given
  (h: x < y) :
-- imply
  ∃ z:ℚ, x < z ∧ z < y :=
-- proof
  Rat.exists_between_rat h


-- created on 2026-10-20
