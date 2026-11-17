module

public import Theorem.Rat.DivMulS.eq.Div.of.Ne_0
public import Theorem.Rat.MulDivS.eq.DivMulS

public section

open Nat Rat


public theorem Rat.MulDivS.eq.Div.of.Ne_0
  [Semifield α]
  {a : α}
-- given
  (h : a ≠ 0)
  (n d : α) :
-- imply
  (n / a) * (a / d) = n / d := by
-- proof
  rw [MulDivS.eq.DivMulS]
  rw [Mul.comm (a := a)]
  apply DivMulS.eq.Div.of.Ne_0 h


-- created on 2025-12-09
