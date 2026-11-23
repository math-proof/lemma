module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_3_1.Part5
public import Theorem.Nat.Nat.eq.Object
public import Theorem.Nat.Nat.is.Eq

public section

open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Object
open Nat


/--
[SetTheory.Object.natCast_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
public theorem main
  [SetTheory]
  {n m:ℕ} :
-- imply
  (n : Object) = (m : Object) ↔ n = m :=
-- proof
  by
    simp [←_root_.Nat.Nat.eq.Object, Subtype.val_inj, Nat.is.Eq]


-- created on 2026-10-22
-- updated on 2026-10-26
