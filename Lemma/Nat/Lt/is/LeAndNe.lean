import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_2.Part2
open EReal


/--
[EReal.lt_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {x y:EReal} :
-- imply
  x < y ↔ x ≤ y ∧ x ≠ y :=
-- proof
  EReal.lt_iff x y


-- created on 2026-10-22
