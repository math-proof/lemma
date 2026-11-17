module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LtCoeS.is.Lt |
| comm | Nat.Lt.is.LtCoeS |
| mp   | Nat.Lt.of.LtCoeS |
| mpr  | Nat.LtCoeS.of.Lt |
| mp.comm | Nat.Gt.of.GtCoeS |
| mpr.comm | Nat.GtCoeS.of.Gt |
| comm.is | Nat.GtCoeS.is.Gt |
-/
@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Nat.LtCoeS.is.Lt
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (a b : ℕ) :
-- imply
  (a : R) < (b : R) ↔ a < b :=
-- proof
  Nat.cast_lt



public theorem Nat.LtCoeS.of.Lt
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ} (h : a < b) : (a : R) < (b : R) :=
  (Nat.LtCoeS.is.Lt a b).mpr h

public theorem Nat.GtCoeS.of.Gt
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
  {a b : ℕ} (h : a > b) : (a : R) > (b : R) :=
  (Nat.LtCoeS.is.Lt b a).mpr h

-- created on 2025-03-29
-- updated on 2026-10-26
