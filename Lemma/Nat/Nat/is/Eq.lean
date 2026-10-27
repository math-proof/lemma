import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.nat_equiv_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n m:ℕ} :
-- imply
  (n:Chapter3.Nat) = (m:Chapter3.Nat) ↔ n=m :=
-- proof
  Equiv.apply_eq_iff_eq Chapter3.SetTheory.Set.nat_equiv


-- created on 2026-10-22
-- updated on 2026-10-26
