module

public import Theorem.Nat.Mul_Add.eq.AddMulS

public section

open Nat


public theorem Nat.AddMul.eq.Mul_Add_1
  [Semiring α]
  {k d : α} :
-- imply
  d * k + d = d * (k + 1) := by
-- proof
  rw [Mul_Add.eq.AddMulS]
  simp


-- created on 2025-05-06
