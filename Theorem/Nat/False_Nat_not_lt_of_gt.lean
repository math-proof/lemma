module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.Le.of.Lt_Nat_le_of_lt
public import Theorem.Nat.Ne_Nat_ne_of_lt

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.not_lt_of_gt](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
public theorem main
  {a b:Chapter2.Nat} :
-- imply
  a < b ∧ a > b → False :=
-- proof
  by
    intro h
    have := (ge_antisymm (Le.of.Lt_Nat_le_of_lt h.1) (Le.of.Lt_Nat_le_of_lt h.2)).symm
    have := Ne_Nat_ne_of_lt h.1
    contradiction


-- created on 2026-10-22
-- updated on 2026-10-26
