module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.All.of.All_Nat_induction
public import Theorem.Nat.Eq0Add
public import Theorem.Nat.Eq_Add

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_succ](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private theorem main
  {n m:Chapter2.Nat} :
-- imply
  n + (m++) = (n + m)++ :=
-- proof
  by
    revert n
    apply All.of.All_Nat_induction
    · rw [Eq0Add, Eq0Add]
    intro n ih
    rw [Eq_Add, ih]
    rw [Eq_Add]


-- created on 2026-10-22
-- updated on 2026-10-26
