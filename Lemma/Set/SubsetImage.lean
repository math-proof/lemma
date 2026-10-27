import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.image_in_codomain](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {f:X → Y}
  {S: Chapter3.Set} :
-- imply
  image f S ⊆ Y :=
-- proof
  Chapter3.SetTheory.Set.image_in_codomain f S


-- created on 2026-10-22
