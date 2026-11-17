module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LeCoeS.is.Le |
| comm | Nat.Le.is.LeCoeS |
| mp   | Nat.Le.of.LeCoeS |
| mpr  | Nat.LeCoeS.of.Le |
| mp.comm | Nat.Ge.of.GeCoeS |
| mpr.comm | Nat.GeCoeS.of.Ge |
| comm.is | Nat.GeCoeS.is.Ge |
-/
@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Nat.LeCoeS.is.Le
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (a b : ℕ) :
-- imply
  (a : R) ≤ (b : R) ↔ a ≤ b :=
-- proof
  Nat.cast_le



public theorem Nat.GeCoeS.of.Ge
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ} (h : a ≥ b) : (a : R) ≥ (b : R) :=
  (Nat.LeCoeS.is.Le b a).mpr h


public theorem Nat.LeCoeS.of.Le
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ} (h : a ≤ b) : (a : R) ≤ (b : R) :=
  (Nat.LeCoeS.is.Le a b).mpr h

-- created on 2025-03-29
-- updated on 2026-10-26
