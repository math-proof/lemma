module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Rat.Div.eq.Mul_Inv
public import Theorem.Int.MulSub.eq.SubMulS

public section

open Int Rat


@[comm]
public theorem Rat.Sub_Div.eq.DivSubMul.of.Ne_0
  [DivisionRing α]
  {b : α}
-- given
  (h : b ≠ 0)
  (x a : α) :
-- imply
  x - a / b = (x * b - a) / b := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [MulSub.eq.SubMulS]
  simp [h]


public theorem Rat.DivSubMul.eq.Sub_Div.of.Ne_0
  [DivisionRing α]
  {b : α}
  (h : b ≠ 0)
  (x a : α) :
  (x * b - a) / b = x - a / b :=
  (Rat.Sub_Div.eq.DivSubMul.of.Ne_0 h x a).symm

-- created on 2025-01-14
