module

public section


public theorem Nat.EqMin.of.Le
  [LinearOrder α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  a ⊓ b = a := by
-- proof
  simp [h]


-- created on 2018-10-14
