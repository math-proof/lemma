module

public section


public theorem Nat.Min.eq.IteLe
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b = if a ≤ b then
    a
  else
    b :=
-- proof
  min_def a b


-- created on 2018-08-07
