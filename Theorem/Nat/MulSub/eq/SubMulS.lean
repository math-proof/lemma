module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Nat.MulSub.eq.SubMulS
-- given
  (x a b : ℕ) :
-- imply
  (a - b) * x = a * x - b * x :=
-- proof
  Nat.sub_mul a b x


-- created on 2025-10-16
