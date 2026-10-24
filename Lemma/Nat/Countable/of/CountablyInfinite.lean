import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_1
open Chapter8
open Chapter8.CountablyInfinite


/--
[CountablyInfinite.toCountable](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X : Type}
-- given
  (hX: CountablyInfinite X) :
-- imply
  Countable X :=
-- proof
  Chapter8.CountablyInfinite.toCountable hX


-- created on 2026-10-22
