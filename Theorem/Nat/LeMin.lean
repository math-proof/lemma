module

public import Mathlib

public section


public theorem Nat.LeMin.left
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b ≤ a := by
-- proof
  simp


public theorem Nat.LeMin
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b ≤ b := by
-- proof
  simp


-- created on 2023-04-23
