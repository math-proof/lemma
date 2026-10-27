import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_3_fn
import Lemma.Set.EqIffP
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


/--
[SetTheory.Set.f_3_3_3c_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x: (Chapter3.Nat \ {(0:Object)}: Chapter3.Set)}
  {y: Chapter3.Nat} :
-- imply
  y = f_3_3_3c x ↔ ((y+1:ℕ):Object) = x :=
-- proof
  EqIffP


-- created on 2026-10-22
-- updated on 2026-10-26
