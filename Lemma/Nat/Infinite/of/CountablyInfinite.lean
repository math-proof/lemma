import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_1.Part4
open Chapter8
open Chapter8.CountablyInfinite


/--
[CountablyInfinite.toInfinite](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X : Type}
-- given
  (hX: CountablyInfinite X) :
-- imply
  Infinite X :=
-- proof
  Chapter8.CountablyInfinite.toInfinite hX


-- created on 2026-10-22
