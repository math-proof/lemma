module

public section


public theorem Bool.Eq.of.HEq
  {a : α}
  {b : β}
-- given
  (h : HEq a b) :
-- imply
  α = β :=
-- proof
  type_eq_of_heq h


-- created on 2025-07-15
