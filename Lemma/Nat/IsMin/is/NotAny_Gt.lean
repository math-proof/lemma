import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_5
open Chapter8
open Chapter8.IsMin


/--
[IsMin.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  {X:Type} [PartialOrder X]
  {x:X} :
-- imply
  IsMin x ↔ ¬ ∃ y, x > y :=
-- proof
  Chapter8.IsMin.iff x


-- created on 2026-10-22
