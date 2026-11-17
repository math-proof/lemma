module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Rat.Div.eq.Mul_Inv
public import Theorem.Int.MulSub.eq.SubMulS

public section

open Int Rat


@[comm]
public theorem Rat.DivSub.eq.SubDivS
  [DivisionRing α]
  {x y a : α} :
-- imply
  (x - y) / a = x / a - y / a := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [SubMulS.eq.MulSub]


-- created on 2025-03-02
