module

public import Initialize.Tactic.Attr.Basic

public section


public theorem Nat.MulMul.comm
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = a * c * b := by
-- proof
  grind


public theorem Nat.MulMul.swap
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = b * a * c := by
-- proof
  grind


public theorem Nat.MulMul.reverse
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = c * b * a := by
-- proof
  grind


@[comm]
public theorem Nat.MulMul.rotate
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = b * c * a := by
-- proof
  grind


-- created on 2024-11-29
-- updated on 2026-10-26
