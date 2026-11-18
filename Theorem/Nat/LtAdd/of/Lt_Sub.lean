module

public import Mathlib

public section


public theorem Nat.LtAdd.of.Lt_Sub
  {a b c : ℕ}
-- given
  (h : a < c - b) :
-- imply
  a + b < c :=
-- proof
  Nat.add_lt_of_lt_sub h


public theorem Nat.LtAdd.of.Lt_Sub.left
  {a b c : ℕ}
-- given
  (h : b < c - a) :
-- imply
  a + b < c :=
-- proof
  Nat.add_lt_of_lt_sub' h


-- created on 2025-04-06
-- updated on 2026-10-26
