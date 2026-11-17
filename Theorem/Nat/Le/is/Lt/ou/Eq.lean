module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Le.is.Lt.ou.Eq |
| comm | Nat.Lt.ou.Eq.is.Le |
| mp   | Nat.Lt.ou.Eq.of.Le |
| mpr  | Nat.Le.of.Lt.ou.Eq |
| mp.comm | Nat.Eq.ou.Lt.of.Ge |
-/
@[comm, mp, mpr, mp.comm]
public theorem Nat.Le.is.Lt.ou.Eq
  [PartialOrder α]
-- given
  (a b : α) :
-- imply
  a ≤ b ↔ a < b ∨ a = b :=
-- proof
  le_iff_lt_or_eq



public theorem Nat.Lt.ou.Eq.of.Le
  [PartialOrder α]
  {a b : α} (h : a ≤ b) : a < b ∨ a = b :=
  (Nat.Le.is.Lt.ou.Eq a b).mp h


public theorem Nat.Eq.ou.Lt.of.Ge
  [PartialOrder α]
  {a b : α} (h : a ≥ b) : a = b ∨ b < a :=
  match (Nat.Le.is.Lt.ou.Eq b a).mp h with
  | Or.inl hlt => Or.inr hlt
  | Or.inr heq => Or.inl heq.symm

-- created on 2025-03-29
-- updated on 2026-10-26
