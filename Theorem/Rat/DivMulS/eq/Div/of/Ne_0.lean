module

public import Theorem.Nat.MulMul.eq.Mul_Mul
public import Theorem.Rat.Div.eq.Mul_Inv

public section

open Nat Rat


public theorem Rat.DivMulS.eq.Div.of.Ne_0
  [DivisionSemiring α]
  {n d a : α}
-- given
  (h : a ≠ 0) :
-- imply
  (n * a) / (d * a) = n / d := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [mul_inv_rev]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul_Mul.eq.MulMul (a := a)]
  simp [h]
  rw [Div.eq.Mul_Inv]


public theorem left
  [Semifield α]
  {a n d : α}
-- given
  (h : a ≠ 0) :
-- imply
  (a * n) / (a * d) = n / d := by
-- proof
  repeat rw [Mul.comm (a := a)]
  apply main h


-- created on 2025-04-06
-- updated on 2025-12-17
