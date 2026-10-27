import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.mem_preimage'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {f:X → Y}
  {U: Chapter3.Set}
  {x:Object} :
-- imply
  x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U :=
-- proof
  Chapter3.SetTheory.Set.mem_preimage' f U x


-- created on 2026-10-22
