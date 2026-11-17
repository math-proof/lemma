module

public import Theorem.Nat.Le.of.Lt

public section

open Nat


public theorem Nat.Ge.of.Gt
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≥ y :=
-- proof
  Le.of.Lt h


public theorem relax
  {x y : ℤ}
-- given
  (h : x > y - 1) :
-- imply
  x ≥ y := by
-- proof
  omega

-- created on 2018-06-28
-- updated on 2025-04-04
-- updated on 2026-09-27
