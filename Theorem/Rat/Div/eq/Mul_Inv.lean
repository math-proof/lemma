module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Rat.Div.eq.Mul_Inv
  [DivInvMonoid α]
-- given
  (a b : α) :
-- imply
  a / b = a * b⁻¹ :=
-- proof
  div_eq_mul_inv a b



public theorem Rat.Mul_Inv.eq.Div
  [DivInvMonoid α]
  (a b : α) :
  a * b⁻¹ = a / b :=
  (Rat.Div.eq.Mul_Inv a b).symm

-- created on 2024-07-01
-- updated on 2026-10-26
