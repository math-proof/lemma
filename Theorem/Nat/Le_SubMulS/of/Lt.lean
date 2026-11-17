module

public import Theorem.Nat.AddMul.le.Mul
public import Theorem.Nat.Le_Sub.of.LeAdd
public import Mathlib

public section

open Nat


public theorem Nat.Le_SubMulS.of.Lt.left
  {n : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  m ≤ m * n - m * i := by
-- proof
  have h := AddMul.le.Mul.of.Lt h m
  apply Le_Sub.of.LeAdd
  rwa [Nat.add_comm]


public theorem Nat.Le_SubMulS.of.Lt
  {n : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  m ≤ n * m - i * m := by
-- proof
  rw [Nat.mul_comm n m]
  rw [Nat.mul_comm i m]
  apply Nat.Le_SubMulS.of.Lt.left h


-- created on 2025-05-31
