import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_1
open Chapter8
open Chapter8.CountablyInfinite


/--
[CountablyInfinite.iff'](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  CountablyInfinite X ↔ Countable X ∧ Infinite X :=
-- proof
  Chapter8.CountablyInfinite.iff' X


-- created on 2026-10-22
