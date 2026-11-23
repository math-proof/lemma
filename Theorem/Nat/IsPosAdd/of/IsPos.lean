module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.All.of.All_Nat_induction
public import Theorem.Nat.Eq_Add0
public import Theorem.Nat.AddEqAdd

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_pos_left](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
public theorem main
  {a b : Chapter2.Nat}
-- given
  (ha: a.IsPos) :
-- imply
  (a + b).IsPos :=
-- proof
  by
    revert b
    apply All.of.All_Nat_induction
    · rwa [Eq_Add0]
    intro b hab
    rw [AddEqAdd]
    have : (a + b)++ ≠ 0 := succ_ne _
    exact this


-- created on 2026-10-22
-- updated on 2026-10-26
