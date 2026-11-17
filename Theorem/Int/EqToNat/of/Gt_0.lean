module

public import Theorem.Int.EqToNat.of.Ge_0
public import Theorem.Nat.Ge.of.Gt

public section

open Int Nat


@[comm]
public theorem Int.EqToNat.of.Gt_0
  {n : ℤ}
-- given
  (h : n > 0) :
-- imply
  n.toNat = n :=
-- proof
  EqToNat.of.Ge_0 (Ge.of.Gt h)


-- created on 2025-05-04
-- updated on 2025-10-25
