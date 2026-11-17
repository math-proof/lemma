module

public import Theorem.Nat.Add
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[comm 1]
public theorem Nat.Lt_Sub.of.LtAdd
  {a b c : ℕ}
-- given
  (h : a + b < c) :
-- imply
  a < c - b :=
-- proof
  Nat.lt_sub_of_add_lt h


@[comm 1]
public theorem left
  {a b c : ℕ}
-- given
  (h : a + b < c) :
-- imply
  b < c - a := by
-- proof
  rw [Nat.Add.Comm] at h
  apply Nat.Lt_Sub.of.LtAdd h


-- created on 2025-10-10
