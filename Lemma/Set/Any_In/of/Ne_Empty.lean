import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
import Lemma.Set.All_Empty
import Lemma.Set.Eq.of.All_In
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Set


/--
[SetTheory.Set.nonempty_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set}
-- given
  (h: X ≠ ∅) :
-- imply
  ∃ x, x ∈ X :=
-- proof
  by
    -- This proof is written to follow the structure of the original text.
    by_contra! this
    have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by simp [this, All_Empty]
    apply Eq.of.All_In at claim
    contradiction


-- created on 2018-09-06
-- updated on 2026-10-23
