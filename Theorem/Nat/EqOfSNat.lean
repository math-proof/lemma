module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_3_1.Part5
public import Theorem.Nat.Nat.is.Eq

public section

open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Nat


/--
[SetTheory.Set.ofNat_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {n m:ℕ} :
-- imply
  (OfNat.ofNat n : Chapter3.Nat) = (OfNat.ofNat m : Chapter3.Nat) ↔ OfNat.ofNat n = OfNat.ofNat m :=
-- proof
  by
    convert Nat.is.Eq


-- created on 2026-10-22
-- updated on 2026-10-26
