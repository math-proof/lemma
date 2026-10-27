import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Object


/--
[SetTheory.Object.ofnat_eq'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ} :
-- imply
  (OfNat.ofNat n:Object) = (n:Object) :=
-- proof
  rfl


-- created on 2026-10-22
-- updated on 2026-10-26
