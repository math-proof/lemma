import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_3.Part2
import Lemma.Set.Eq.is.All_Eq
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


/--
[SetTheory.Set.comp_assoc](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {W X Y Z: Chapter3.Set}
  {g: Function X Y}
  {f: Function W X}
-- given
  (h: Function Y Z) :
-- imply
  h ○ (g ○ f) = (h ○ g) ○ f :=
-- proof
  by
    simp [Eq.is.All_Eq]


-- created on 2026-10-22
-- updated on 2026-10-26
