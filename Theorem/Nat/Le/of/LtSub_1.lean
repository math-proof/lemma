module

public import Theorem.Nat.NotLe.is.Gt
public import Theorem.Nat.Le_Sub_1.of.Lt
public import Theorem.Nat.Lt.of.Lt.Le

public section

open Nat


@[comm 1]
public theorem Nat.Le.of.LtSub_1
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x - 1 < y) :
-- imply
  x ≤ y := by
-- proof
  by_contra h'
  have := Gt.of.NotLe h'
  have := GeSub_1.of.Gt this
  have := Lt.of.Lt.Le h this
  simp at this


-- created on 2025-05-05
-- updated on 2025-05-06
