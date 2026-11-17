module

public import Theorem.Nat.Add
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[comm]
public theorem Int.SubAdd.eq.Add_Sub
  [SubNegMonoid α]
-- given
  (a b c : α) :
-- imply
  a + b - c = a + (b - c) :=
-- proof
  add_sub_assoc a b c


@[comm]
public theorem Int.SubAdd.eq.Add_Sub.comm
  [AddCommGroup α]
-- given
  (a b c : α) :
-- imply
  a + b - c = b + (a - c) := by
-- proof
  rw [Nat.Add.Comm]
  rw [Int.SubAdd.eq.Add_Sub]


-- created on 2024-07-01
-- updated on 2026-07-07
