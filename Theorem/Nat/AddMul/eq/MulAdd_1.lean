module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Nat.MulAdd.eq.AddMulS

public section

open Nat


@[comm]
public theorem Nat.AddMul.eq.MulAdd_1
  [Semiring α]
  {k d : α} :
-- imply
  k * d + d = (k + 1) * d := by
-- proof
  simp [MulAdd.eq.AddMulS]



public theorem Nat.MulAdd_1.eq.AddMul
  [Semiring α]
  {k d : α} :
  (k + 1) * d = k * d + d :=
  (Nat.AddMul.eq.MulAdd_1).symm

-- created on 2025-03-30
