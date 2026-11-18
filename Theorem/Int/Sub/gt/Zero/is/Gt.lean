module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Int.Sub.gt.Zero.is.Lt

public section

open Int


/--
This lemma establishes that in an additive group with a strict order and right-strict monotonicity, the difference `b - a` being positive is equivalent to `a` being less than `b`.
It leverages the properties of additive groups and the `AddRightStrictMono` typeclass to connect the algebraic operation of subtraction with the order relation.
-/
@[comm, mp, mpr]
public theorem Int.Sub.gt.Zero.is.Gt
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α} :
-- imply
  b - a > 0 ↔ b > a :=
-- proof
  Sub.gt.Zero.is.Lt



public theorem Int.Sub.gt.Zero.of.Gt
  [AddGroup α] [LT α] [AddRightStrictMono α]
  {a b : α} (h : b > a) : b - a > 0 :=
  (Int.Sub.gt.Zero.is.Gt).mpr h

-- created on 2025-08-02
-- updated on 2025-10-16
