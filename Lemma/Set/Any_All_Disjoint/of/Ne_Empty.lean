import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_2
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.axiom_of_regularity](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_2.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A:Chapter3.Set}
-- given
  (h: A ≠ ∅) :
-- imply
  ∃ x:A, ∀ S:Chapter3.Set, x.val = S → Disjoint S A :=
-- proof
  by
    choose x hx hx' using regularity_axiom A (nonempty_def h)
    use ⟨x, hx⟩
    intro S hS
    specialize hx' S hS
    rw [disjoint_iff, eq_empty_iff_forall_notMem]
    intro z hz
    exact hx' ⟨z, ((Chapter3.SetTheory.Set.mem_inter z S A).mp hz).2, ((Chapter3.SetTheory.Set.mem_inter z S A).mp hz).1⟩


-- created on 2026-10-22
-- updated on 2026-10-26
