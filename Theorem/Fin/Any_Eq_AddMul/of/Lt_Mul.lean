module

public import Theorem.Nat.Any_EqAddMul.of.Lt_Mul
public import Mathlib

public section

open Nat


public theorem Fin.Any_Eq_AddMul.of.Lt_Mul
  {m n : ℕ}
-- given
  (h : t < m * n) :
-- imply
  ∃ (i : Fin m) (j : Fin n), t = i * n + j := by
-- proof
  have := Any_EqAddMul.of.Lt_Mul h
  aesop


-- created on 2025-12-01
