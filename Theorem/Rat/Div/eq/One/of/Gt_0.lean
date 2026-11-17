module

public import Theorem.Nat.Ne.of.Gt
public import Theorem.Rat.Div.eq.One.of.Ne_0

public section

open Rat Nat


public theorem Rat.Div.eq.One.of.Gt_0
  [Preorder α]
  [GroupWithZero α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  x / x = 1 :=
-- proof
  (Div.eq.One.of.Ne_0 ∘ Ne.of.Gt) h


-- created on 2024-11-25
