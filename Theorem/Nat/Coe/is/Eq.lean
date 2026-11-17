module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm, mp, mpr]
public theorem Nat.Coe.is.Eq
  [AddMonoidWithOne R]
  [CharZero R]
  {a b : ℕ} :
-- imply
  (a : R) = (b : R) ↔ a = b :=
-- proof
  Nat.cast_inj



public theorem Nat.Eq.of.Coe
  [AddMonoidWithOne R]
  [CharZero R]
  {a b : ℕ} (h : (a : R) = (b : R)) : a = b :=
  (Nat.Coe.is.Eq).mp h

-- created on 2025-04-11
-- updated on 2026-10-26
