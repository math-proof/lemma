import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.Example_3_6_8_c](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  :
-- imply
  ¬({0,1,2}:Chapter3.Set) ≈ ({3,4}:Chapter3.Set) :=
-- proof
  Chapter3.SetTheory.Set.Example_3_6_8_c


-- created on 2026-10-22
