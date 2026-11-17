module

public import Instance.Data.Int.Integers
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


@[comm 1]
public theorem Nat.LeAdd_1.of.Lt
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x < y) :
-- imply
  x + 1 ≤ y :=
-- proof
  IntegerRing.succ_le_of_lt h


-- created on 2018-10-14
