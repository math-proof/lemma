module

public import Theorem.Nat.EqAddMulDiv
public import Theorem.Nat.LtDiv.of.Lt_Mul
public import Theorem.Nat.LtMod.of.Gt_0
public import Theorem.Nat.Gt_0.of.GtMul

public section

open Nat


public theorem left
  {k n m : ℕ}
-- given
  (h : k < n * m) :
-- imply
  ∃ (i : Fin m) (j : Fin n), i * n + j = k := by
-- proof
  have hn := Gt_0.of.GtMul.left h
  have h_lt := LtMod.of.Gt_0 hn k
  use ⟨k / n, LtDiv.of.Lt_Mul.left h⟩, ⟨k % n, h_lt⟩
  apply EqAddMulDiv


public theorem Nat.Any_EqAddMul.of.Lt_Mul
  {k n m : ℕ}
-- given
  (h : k < m * n) :
-- imply
  ∃ (i : Fin m) (j : Fin n), i * n + j = k := by
-- proof
  rw [Mul.comm] at h
  apply left h


-- created on 2025-05-29
