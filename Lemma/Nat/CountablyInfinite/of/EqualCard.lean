import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_1
open Chapter8
open Chapter8.CountablyInfinite


/--
[CountablyInfinite.equiv](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X Y: Type}
-- given
  (hXY : EqualCard X Y) :
-- imply
  CountablyInfinite X ↔ CountablyInfinite Y :=
-- proof
  Chapter8.CountablyInfinite.equiv hXY


-- created on 2026-10-22
