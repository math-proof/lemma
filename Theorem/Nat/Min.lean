module

public import Mathlib

public section


public theorem Nat.Min.comm
  [LinearOrder α]
  {a b : α} :
-- imply
  a ⊓ b = b ⊓ a :=
-- proof
  min_comm a b


-- created on 2025-06-06
