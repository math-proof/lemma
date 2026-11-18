module

public section


public theorem Bool.IffEqS.of.Eq
  {a b : α}
-- given
  (h : a = b) :
-- imply
  a = x ↔ b = x := by
-- proof
  rw [h]


public theorem Bool.IffEqS.of.Eq.left
  {a b : α}
-- given
  (h : a = b) :
-- imply
  x = a ↔ x = b := by
-- proof
  rw [h]


-- created on 2025-05-29
