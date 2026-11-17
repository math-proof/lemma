module

public import Theorem.Nat.Gt_0.of.Gt
public import Theorem.Nat.Gt_0.of.Lt0Mul
public import Theorem.Nat.Mul

public section

open Nat


public theorem left
  {k n m : ℕ}
-- given
  (h : n * m > k) :
-- imply
  n > 0 :=
-- proof
  (Gt_0.of.Lt0Mul.left ∘ Gt_0.of.Gt) h


public theorem Nat.Gt_0.of.GtMul
  {k n m : ℕ}
-- given
  (h : n * m > k) :
-- imply
  m > 0 := by
-- proof
  rw [Mul.comm] at h
  apply left h


-- created on 2025-05-29
-- updated on 2025-07-08
