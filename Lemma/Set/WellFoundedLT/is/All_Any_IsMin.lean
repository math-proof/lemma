import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Section_8_5.Part4
open Chapter8
open Chapter8.WellFoundedLT


/--
[WellFoundedLT.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_5.lean)
-/
@[path]
private lemma main
  {X : Type} [LinearOrder X]
  :
-- imply
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x :=
-- proof
  Chapter8.WellFoundedLT.iff X


-- created on 2026-10-22
