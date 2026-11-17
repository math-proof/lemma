module

public import Theorem.Nat.Ge.of.Gt
public import Theorem.Nat.EqMin.of.Ge

public section

open Nat


public theorem Nat.EqMin.of.Gt
  [LinearOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ⊓ b = b := 
-- proof
  EqMin.of.Ge (Ge.of.Gt h)


-- created on 2018-09-09
-- updated on 2025-10-12
