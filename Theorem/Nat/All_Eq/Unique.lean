module

public import Mathlib
public import Abbrev.Analysis.Section_2_1
public import Theorem.Nat.EqRecurseNat0
public import Theorem.Nat.EqRecurse
public import Theorem.Nat.EqAndAll_Eq.is.Eq_Recurse

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.recurse_uniq](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
public theorem Nat.All_Eq.Unique
  {f: Chapter2.Nat → Chapter2.Nat → Chapter2.Nat}
  {c: Chapter2.Nat} :
-- imply
  ∃! (a: Chapter2.Nat → Chapter2.Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) :=
-- proof
  by
    apply ExistsUnique.intro (recurse f c)
    ·
      constructor
      · exact EqRecurseNat0
      exact fun n ↦ EqRecurse
    intro a
    exact EqAndAll_Eq.is.Eq_Recurse.mp


-- created on 2026-10-22
-- updated on 2026-10-26
