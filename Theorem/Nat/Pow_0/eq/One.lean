module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_3.Part2
public import Theorem.Nat.EqRecurseNat0
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


public section

/--
[Nat.pow_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private theorem main
  {m: Chapter2.Nat} :
-- imply
  m ^ (0:Chapter2.Nat) = 1 :=
-- proof
  EqRecurseNat0 (f := fun _ prod ↦ prod * m)


-- created on 2026-10-22
-- updated on 2026-10-26
