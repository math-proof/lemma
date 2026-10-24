import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_5
open Chapter8
open Chapter8.IsTotal


/--
[IsTotal.subtype](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  {X:Type} [PartialOrder X]
  {A: Set X}
-- given
  (hA: IsTotal X) :
-- imply
  IsTotal A :=
-- proof
  Chapter8.IsTotal.subtype hA


-- created on 2026-10-22
