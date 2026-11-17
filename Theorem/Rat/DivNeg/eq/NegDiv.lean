module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Rat.DivNeg.eq.NegDiv
  [DivisionMonoid α] [HasDistribNeg α]
-- given
  (a b : α) :
-- imply
  -a / b = -(a / b) :=
-- proof
  neg_div b a


-- created on 2024-07-01
