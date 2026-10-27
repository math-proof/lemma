import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.nonempty_of_inhabited](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set}
  {x:Object}
-- given
  (h:x ∈ X) :
-- imply
  X ≠ ∅ :=
-- proof
  by
    contrapose! h
    rw [eq_empty_iff_forall_notMem] at h
    exact h x


-- created on 2026-10-22
-- updated on 2026-10-26
