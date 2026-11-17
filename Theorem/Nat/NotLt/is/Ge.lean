module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.NotLt.is.Ge |
| comm | Nat.Ge.is.NotLt |
| mp | Nat.Ge.of.NotLt |
| mp.comm | Nat.Le.of.NotGt |
-/
@[comm, mp, mp.comm]
public theorem Nat.NotLt.is.Ge
  [LinearOrder α]
  {a b : α} :
-- imply
  ¬a < b ↔ a ≥ b :=
-- proof
  not_lt



public theorem Nat.Ge.of.NotLt
  [LinearOrder α]
  {a b : α} (h : ¬a < b) : a ≥ b :=
  (Nat.NotLt.is.Ge).mp h

-- created on 2025-04-18
