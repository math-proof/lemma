module

public import Theorem.Nat.Add
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[comm, mp, mpr]
public theorem Nat.LtSub.is.Lt_Add.of.Ge.right
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
  rw [LtSub.is.Lt_Add.of.Ge.right h]
  rw [Nat.Add.Comm]


public theorem Nat.LtSub.of.Lt_Add.Ge
  {a b c : ℕ}
  (h₀ : a ≥ b)
  (h₁ : a < b + c) :
  a - b < c :=
  (Nat.LtSub.is.Lt_Add.of.Ge h₀ c).mpr h₁


-- created on 2025-08-02
