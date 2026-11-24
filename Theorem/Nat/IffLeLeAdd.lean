module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.Ge.is.Add.ge.Add

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_le_add_left](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private theorem main
  {a b c:Chapter2.Nat} :
-- imply
  a ≤ b ↔ c + a ≤ c + b :=
-- proof
  Ge.is.Add.ge.Add


-- created on 2026-10-22
-- updated on 2026-10-26
