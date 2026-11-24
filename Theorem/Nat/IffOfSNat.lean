module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_3_1.Part5
public import Theorem.Nat.Nat.is.Eq
public import Theorem.Nat.OfNat.eq.Object
public import Theorem.Nat.Nat.eq.Object
public import Theorem.Set.Val.is.Eq

public section

open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Nat
open Set


/--
[SetTheory.Set.ofNat_inj'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private theorem main
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
