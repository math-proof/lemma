module

public import Mathlib

public section


public theorem Nat.NotGt
  [Preorder α]
  {a : α} :
-- imply
  ¬(a > a) :=
-- proof
  lt_irrefl a


-- created on 2025-03-27
