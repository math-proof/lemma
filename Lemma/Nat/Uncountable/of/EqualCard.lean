import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_8_3
open Chapter8
open Chapter8.Uncountable


/--
[Uncountable.equiv](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_3.lean)
-/
@[path]
private lemma main
  {X Y: Type}
-- given
  (hXY : EqualCard X Y) :
-- imply
  Uncountable X ↔ Uncountable Y :=
-- proof
  Chapter8.Uncountable.equiv hXY


-- created on 2026-10-22
