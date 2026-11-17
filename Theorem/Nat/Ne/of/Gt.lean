module

public import Theorem.Nat.Ne.of.Lt

public section

open Nat


public theorem Nat.Ne.of.Gt
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≠ y :=
-- proof
  (Ne.of.Lt h).symm


-- created on 2021-09-06
-- updated on 2025-04-04
