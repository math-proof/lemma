module

public import Theorem.Nat.Ne_0.of.Lt0Mul
public import Theorem.Nat.Gt_0.of.Ne_0

public section

open Nat


public theorem left
  {a b : ℕ}
-- given
  (h : a * b > 0) :
-- imply
  a > 0 := by
-- proof
  have := Ne_0.of.Lt0Mul.left h
  apply Gt_0.of.Ne_0 this


public theorem Nat.Gt_0.of.Lt0Mul
  {a b : ℕ}
-- given
  (h : a * b > 0) :
-- imply
  b > 0 := by
-- proof
  have := Ne_0.of.Lt0Mul h
  apply Gt_0.of.Ne_0 this


-- created on 2025-06-13
