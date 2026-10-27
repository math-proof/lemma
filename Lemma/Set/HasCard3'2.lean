import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.Example_3_6_8_b](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory] :
-- imply
  ({3,4}:Chapter3.Set).has_card 2 :=
-- proof
  Chapter3.SetTheory.Set.Example_3_6_8_b


-- created on 2026-10-22
