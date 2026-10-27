import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.mem_slice](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x z:Object}
  {Y:Chapter3.Set} :
-- imply
  z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) :=
-- proof
  Chapter3.SetTheory.Set.mem_slice x z Y


-- created on 2026-10-22
