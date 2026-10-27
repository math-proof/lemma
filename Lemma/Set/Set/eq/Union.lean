import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.pair_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {a b:Object} :
-- imply
  ({a,b}:Chapter3.Set) = {a} ∪ {b} :=
-- proof
  by rfl


-- created on 2026-10-22
-- updated on 2026-10-26
