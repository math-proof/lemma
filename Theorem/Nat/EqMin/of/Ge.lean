module

public section


public theorem Nat.EqMin.of.Ge
  [LinearOrder α]
  {a b : α}
-- given
  (h : a ≥ b) :
-- imply
  a ⊓ b = b := by
-- proof
  simp [h]


-- created on 2018-09-04
