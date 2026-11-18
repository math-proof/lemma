module

public import Theorem.Nat.Add
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[comm]
public theorem Nat.AddAdd.eq.Add_Add
  [AddSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = a + (b + c) :=
-- proof
  add_assoc a b c


@[comm]
public theorem Nat.AddAdd.eq.Add_Add.comm
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = a + (c + b) := by
-- proof
  rw [Nat.AddAdd.eq.Add_Add]
  rw [Nat.Add.Comm (a := b)]


public theorem Nat.Add_Add.eq.AddAdd
  [AddSemigroup α]
  (a b c : α) :
  a + (b + c) = a + b + c :=
  (AddAdd.eq.Add_Add a b c).symm


-- created on 2024-07-01
-- updated on 2025-05-24
