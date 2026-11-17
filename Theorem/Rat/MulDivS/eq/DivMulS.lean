module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Rat.MulDivS.eq.DivMulS
  [DivisionCommMonoid α]
  -- given
  (a b x y : α) :
-- imply
  (a / b) * (x / y) = a * x / (b * y) :=
-- proof
  div_mul_div_comm a b x y


-- created on 2025-12-09
