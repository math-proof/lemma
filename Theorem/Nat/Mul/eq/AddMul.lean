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
[Nat.succ_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private theorem main
  {n m: Chapter2.Nat} :
-- imply
  (n++) * m = n * m + m :=
-- proof
  EqRecurse (f := fun _ prod ↦ prod + m)


-- created on 2026-10-22
-- updated on 2026-10-26
