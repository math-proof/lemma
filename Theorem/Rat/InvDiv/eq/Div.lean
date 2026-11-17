module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Rat.InvDiv.eq.Div
  [DivisionMonoid α]
-- given
  (a b : α) :
-- imply
  (a / b)⁻¹ = b / a := 
-- proof
  inv_div a b


-- created on 2025-12-08
