module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.NotLe.is.Gt |
| comm | Nat.Gt.is.NotLe |
| mp | Nat.Gt.of.NotLe |
| mp.comm | Nat.Lt.of.NotGe |
-/
@[comm, mp, mp.comm]
public theorem Nat.NotLe.is.Gt
  [LinearOrder α]
  {a b : α} :
-- imply
  ¬(a ≤ b) ↔ a > b :=
-- proof
  not_le


-- created on 2025-03-29
-- updated on 2026-10-26
