module

public import Instance.Data.Int.Integers

public section


public theorem Nat.LtMod.of.Gt_0
  [IntegerRing Z]
  {d : Z}
-- given
  (h : d > 0)
  (n : Z) :
-- imply
  n % d < d :=
-- proof
  IntegerRing.mod_lt h n


-- created on 2025-03-20
-- updated on 2026-10-26
