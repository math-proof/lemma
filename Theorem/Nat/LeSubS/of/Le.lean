module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


@[comm 1]
public theorem Nat.LeSubS.of.Le
  {x y : ℕ}
-- given
  (h : x ≤ y)
  (z : ℕ) :
-- imply
  x - z ≤ y - z :=
-- proof
  Nat.sub_le_sub_right h z


public theorem Nat.GeSubS.of.Ge
  {x y : ℕ}
  (h : x ≥ y)
  (z : ℕ) :
  x - z ≥ y - z :=
  Nat.sub_le_sub_right h z


-- created on 2024-07-01
-- updated on 2026-10-26
