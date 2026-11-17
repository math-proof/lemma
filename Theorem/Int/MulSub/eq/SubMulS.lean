module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Int.MulSub.eq.SubMulS
  [NonUnitalNonAssocRing α]
-- given
  (x a b : α) :
-- imply
  (a - b) * x = a * x - b * x :=
-- proof
  sub_mul a b x



public theorem Int.SubMulS.eq.MulSub
  [NonUnitalNonAssocRing α]
  (x a b : α) :
  a * x - b * x = (a - b) * x :=
  (Int.MulSub.eq.SubMulS x a b).symm

-- created on 2024-11-26
-- updated on 2026-10-26
