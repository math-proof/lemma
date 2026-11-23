module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.All.of.All_Nat_induction
public import Theorem.Nat.Eq0Add

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
public theorem main
  {n:Chapter2.Nat} :
-- imply
  n + 0 = n :=
-- proof
  by
    revert n
    apply All.of.All_Nat_induction
    · exact Eq0Add
    intro n ih
    calc
      _ = (n + 0)++ := by rfl
      _ = n++ := by rw [ih]


-- created on 2026-10-22
-- updated on 2026-10-26
