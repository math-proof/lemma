module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.All.of.All_Nat_induction
public import Theorem.Nat.Eq0Add
public import Theorem.Nat.Eq_Add0
public import Theorem.Nat.Eq_Add
public import Theorem.Nat.AddEqAdd

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_comm](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
public theorem main
  {n m:Chapter2.Nat} :
-- imply
  n + m = m + n :=
-- proof
  by
    revert n
    apply All.of.All_Nat_induction
    · rw [Eq0Add, Eq_Add0]
    intro n ih
    rw [Eq_Add]
    rw [AddEqAdd, ih]


-- created on 2026-10-22
-- updated on 2026-10-26
