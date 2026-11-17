module

public import Instance.Data.Int.Integers

public section

public theorem Nat.EqAddSub.of.Ge
  [IntegerRing N]
  {a b : N}
-- given
  (h : b ≥ a) :
-- imply
  b - a + a = b :=
-- proof
  IntegerRing.sub_add_cancel h


-- created on 2025-03-15
-- updated on 2026-11-17
