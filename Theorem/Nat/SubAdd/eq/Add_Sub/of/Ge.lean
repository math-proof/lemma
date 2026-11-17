module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Nat.SubAdd.eq.Add_Sub.of.Ge
  {b c : ℕ}
-- given
  (h : b ≥ c)
  (a : ℕ):
-- imply
  a + b - c = a + (b - c) :=
-- proof
  Nat.add_sub_assoc h a


-- created on 2025-03-31
-- updated on 2026-10-26
