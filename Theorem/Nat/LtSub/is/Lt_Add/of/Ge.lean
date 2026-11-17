module

public import Theorem.Nat.Add
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[comm, mp, mpr]
public theorem right
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  a - b < c ↔ a < c + b :=
-- proof
  Nat.sub_lt_iff_lt_add h


@[comm, mp, mpr]
public theorem Nat.LtSub.is.Lt_Add.of.Ge
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  a - b < c ↔ a < b + c := by
-- proof
  rw [right h]
  rw [Nat.Add.Comm]


-- created on 2025-08-02
