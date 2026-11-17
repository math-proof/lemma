module

public import Theorem.Nat.AddMul.eq.Mul_Add_1
public import Theorem.Nat.LeMulS.of.Ge_0.Le

public section

open Nat


public theorem Nat.AddMul.le.Mul.of.Lt
  {i n : ℕ}
-- given
  (h : i < n) 
  (m : ℕ):
-- imply
  m * i + m ≤ m * n := by
-- proof
  rw [AddMul.eq.Mul_Add_1]
  apply LeMulS.of.Ge_0.Le (by simp) (by linarith)


-- created on 2025-05-31
