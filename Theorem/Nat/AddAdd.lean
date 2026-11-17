module

public import Theorem.Nat.AddAdd.eq.Add_Add

public section

open Nat


public theorem Comm
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = a + c + b := by
-- proof
  repeat rw [Add.comm (b := c)]
  rw [Add_Add.eq.AddAdd]


@[comm]
public theorem rotate
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = b + c + a := by
-- proof
  rw [AddAdd.eq.Add_Add]
  rw [Add.comm]


@[comm]
public theorem swap
  [AddCommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = b + a + c := by
-- proof
  grind


-- created on 2025-06-06
