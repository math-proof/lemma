module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Nat.EqSubAdd

public section

open Nat


@[comm]
public theorem Nat.EqSub.of.EqAdd
  {x y d : ℕ}
-- given
  (h : d + x = y) :
-- imply
  y - x = d := by
-- proof
  rw [← h]
  rw [EqSubAdd]


@[comm]
public theorem left
  {x y d : ℕ}
-- given
  (h : d + x = y) :
-- imply
  y - d = x := by
-- proof
  rw [← h]
  rw [EqSubAdd.left]


-- created on 2025-04-16
-- updated on 2025-10-08
