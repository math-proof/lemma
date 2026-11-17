module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Int.EqToNat.of.Ge_0
  {z : ℤ}
-- given
  (h : z ≥ 0) :
-- imply
  z.toNat = z :=
-- proof
  Int.toNat_of_nonneg h


-- created on 2025-06-07
