module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.Eq_Add
public import Theorem.Nat.EqAdd1

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.two_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private theorem main
  {m:Chapter2.Nat} :
-- imply
  2 + m = (m++)++ :=
-- proof
  by
    rw [show 2 = 1++ from rfl, Eq_Add, EqAdd1]


-- created on 2026-10-22
-- updated on 2026-10-26
