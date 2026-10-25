import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.exists_powerset](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set} :
-- imply
  ∃ (Z: Chapter3.Set), ∀ x, x ∈ Z ↔ ∃ Y:Chapter3.Set, x = Y ∧ Y ⊆ X :=
-- proof
  Chapter3.SetTheory.Set.exists_powerset X


-- created on 2026-10-22
