module

public import Instance.Data.Int.Integers
public import Theorem.Nat.Add

public section

open Nat


public theorem Nat.EqSubAdd.left
  [IntegerRing Z]
  {a b : Z} :
-- imply
  b + a - b = a := by
-- proof
  have := IntegerRing.add_sub_cancel a b
  rwa [Nat.Add.Comm] at this


public theorem Nat.EqSubAdd
  [IntegerRing Z]
  {a b : Z} :
-- imply
  a + b - b = a := by
-- proof
  apply IntegerRing.add_sub_cancel


-- created on 2024-11-27
-- updated on 2025-10-10
