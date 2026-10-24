import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_5
open Chapter8
open Chapter8.IsTotal


/--
[IsTotal.subset](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  {X:Type} [PartialOrder X]
  {A B: Set X}
-- given
  (hA: IsTotal A)
  (hAB: B ⊆ A) :
-- imply
  IsTotal B :=
-- proof
  Chapter8.IsTotal.subset hA hAB


-- created on 2026-10-22
