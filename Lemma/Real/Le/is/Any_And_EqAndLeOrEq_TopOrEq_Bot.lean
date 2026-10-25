import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_2.Part2
open EReal


/--
[EReal.le_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {x y:EReal} :
-- imply
  x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ :=
-- proof
  EReal.le_iff x y


-- created on 2026-10-22
