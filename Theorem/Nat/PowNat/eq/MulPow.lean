module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_3.Part2
public import Theorem.Nat.EqRecurse
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


public section

/--
[Nat.pow_succ](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private theorem main
  {m n: Chapter2.Nat} :
-- imply
  (m:Chapter2.Nat) ^ n++ = m^n * m :=
-- proof
  EqRecurse (f := fun _ prod ↦ prod * m)


-- created on 2026-10-22
-- updated on 2026-10-26
