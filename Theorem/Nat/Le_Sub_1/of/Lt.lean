module

public import Instance.Data.Int.Integers
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


@[comm 1]
public theorem Nat.Le_Sub_1.of.Lt
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : a < b) :
-- imply
  a ≤ b - 1 :=
-- proof
  IntegerRing.le_pred_of_lt h


-- created on 2018-05-05
