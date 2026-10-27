import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Section_8_5.Part4
open Chapter8
open Chapter8.IsStrictUpperBound


/--
[IsStrictUpperBound.iff'](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  {X:Type} [PartialOrder X]
  {A:Set X}
  {x:X} :
-- imply
  IsStrictUpperBound A x ↔ x ∈ upperBounds A \ A :=
-- proof
  Chapter8.IsStrictUpperBound.iff' A x


-- created on 2026-10-22
