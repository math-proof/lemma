import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.union_axiom](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A: Chapter3.Set}
  {x:Object} :
-- imply
  x ∈ union A ↔ ∃ (S:Chapter3.Set), x ∈ S ∧ (S:Object) ∈ A :=
-- proof
  Chapter3.SetTheory.Set.union_axiom A x


-- created on 2026-10-22
