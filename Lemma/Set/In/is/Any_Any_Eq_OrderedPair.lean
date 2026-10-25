import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.mem_cartesian](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {z:Object}
  {X Y:Chapter3.Set} :
-- imply
  z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) :=
-- proof
  Chapter3.SetTheory.Set.mem_cartesian z X Y


-- created on 2026-10-22
