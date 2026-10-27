import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Section_4_2.Part2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.le_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {x y:Section_4_2.Rat} :
-- imply
  x ≤ y ↔ (x < y) ∨ (x = y) :=
-- proof
  Section_4_2.Rat.le_iff x y


-- created on 2026-10-22
