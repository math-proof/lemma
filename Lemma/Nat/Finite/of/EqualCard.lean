import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_1.Part4
open Chapter8
open Chapter8.Finite


/--
[Finite.equiv](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X Y: Type}
-- given
  (hXY : EqualCard X Y) :
-- imply
  Finite X ↔ Finite Y :=
-- proof
  Chapter8.Finite.equiv hXY


-- created on 2026-10-22
