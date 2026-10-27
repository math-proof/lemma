import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Section_8_5.Part4
open Chapter8
open Chapter8.WellFoundedLT


/--
[WellFoundedLT.subset](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  [PartialOrder X]
  {A B: Set X} [hwell: WellFoundedLT A]
-- given
  (hA: IsTotal A)
  (hAB: B ⊆ A) :
-- imply
  WellFoundedLT B :=
-- proof
  Chapter8.WellFoundedLT.subset hA hAB


-- created on 2026-10-22
