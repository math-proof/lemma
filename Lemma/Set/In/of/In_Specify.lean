import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.specification_axiom](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A:Chapter3.Set}
  {P: A → Prop}
  {x:Object}
-- given
  (h: x ∈ A.specify P) :
-- imply
  x ∈ A :=
-- proof
  (SetTheory.specification_axiom A P).1 x h


-- created on 2026-10-22
-- updated on 2026-10-26
