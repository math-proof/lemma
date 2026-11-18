module

public import Mathlib

public section


/--
This lemma applies to Nat, Int as well
-/
public theorem Nat.EqDivMul.of.Ne_0.left
  [CommMonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {a : α}
-- given
  (h : a ≠ 0)
  (b : α) :
-- imply
  a * b / a = b :=
-- proof
  mul_div_cancel_left₀ b h


/--
This lemma applies to Nat, Int as well
-/
public theorem Nat.EqDivMul.of.Ne_0
  [MonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {a : α}
-- given
  (h : a ≠ 0)
  (b : α):
-- imply
  b * a / a = b :=
-- proof
  mul_div_cancel_right₀ b h


-- created on 2024-07-01
-- updated on 2026-10-26
