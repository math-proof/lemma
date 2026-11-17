module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Nat.Sub_Add.eq.SubSub
-- given
  (a b c : ℕ) :
-- imply
  a - (b + c) = a - b - c :=
-- proof
  Nat.sub_add_eq a b c



public theorem Nat.SubSub.eq.Sub_Add
  (a b c : ℕ) :
  a - b - c = a - (b + c) :=
  (Nat.Sub_Add.eq.SubSub a b c).symm

-- created on 2025-10-12
