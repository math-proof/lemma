module

public import Mathlib
public import Abbrev.Analysis.Section_2_1
public import Theorem.Nat.All.of.All_Nat_induction
public import Theorem.Nat.EqRecurse
public import Theorem.Nat.EqRecurseNat0

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.eq_recurse](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
public theorem Nat.EqAndAll_Eq.is.Eq_Recurse
  {f: Chapter2.Nat → Chapter2.Nat → Chapter2.Nat}
  {c: Chapter2.Nat}
  {a: Chapter2.Nat → Chapter2.Nat} :
-- imply
  (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c :=
-- proof
  by
    constructor
    ·
      intro ⟨h0, hsucc⟩
      apply funext
      apply All.of.All_Nat_induction
      · exact h0
      intro n hn
      rw [hsucc n, EqRecurse, hn]
    intro h
    rw [h]
    constructor
    · exact EqRecurseNat0
    exact fun n ↦ EqRecurse


-- created on 2026-10-22
-- updated on 2026-10-26
