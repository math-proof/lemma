import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.iUnion_example](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory] :
-- imply
  iUnion {1,2,3} index_example = {2,3,4,5} :=
-- proof
  Chapter3.SetTheory.Set.iUnion_example


-- created on 2026-10-22
