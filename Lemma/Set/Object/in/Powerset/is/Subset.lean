import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.mem_powerset'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {S S' : Chapter3.Set} :
-- imply
  (S': Object) ∈ S.powerset ↔ S' ⊆ S :=
-- proof
  Chapter3.SetTheory.Set.mem_powerset'


-- created on 2026-10-22
