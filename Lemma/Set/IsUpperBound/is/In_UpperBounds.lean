import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_5
open Chapter8
open Chapter8.IsUpperBound


/--
[IsUpperBound.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  {X:Type} [PartialOrder X]
  {A:Set X}
  {x:X} :
-- imply
  IsUpperBound A x ↔ x ∈ upperBounds A :=
-- proof
  Chapter8.IsUpperBound.iff A x


-- created on 2026-10-22
