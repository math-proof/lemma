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


public theorem Nat.Add_Sub.eq.SubAdd.of.Ge
  {b c : ℕ}
  (h : b ≥ c)
  (a : ℕ) :
  a + (b - c) = a + b - c :=
  (Nat.SubAdd.eq.Add_Sub.of.Ge h a).symm


-- created on 2025-03-31
-- updated on 2026-10-26
