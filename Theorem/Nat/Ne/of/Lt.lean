module

public import Mathlib
public section


public theorem Nat.Ne.of.Lt
  [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≠ y :=
-- proof
  _root_.ne_of_lt h


-- created on 2021-01-12
-- updated on 2026-10-26
