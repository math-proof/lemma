import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
import Lemma.Nat.Nat.is.Eq
import Lemma.Nat.OfNat.eq.Object
import Lemma.Nat.Nat.eq.Object
import Lemma.Set.Val.is.Eq
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Nat
open Set


/--
[SetTheory.Set.ofNat_inj'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n m:ℕ} :
-- imply
  (OfNat.ofNat n : Object) = (OfNat.ofNat m : Object) ↔ OfNat.ofNat n = OfNat.ofNat m :=
-- proof
  by
    simp only [←Nat.eq.Object, OfNat.eq.Object, Val.is.Eq, Nat.is.Eq]
    rfl


-- created on 2026-10-22
-- updated on 2026-10-26
