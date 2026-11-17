module

public import Theorem.Nat.EqAddSub.of.Ge
public import Theorem.Nat.Gt.of.Ge.Gt

open Nat

public section

public theorem Nat.LtSub_1.of.Le.Gt_0
  {x y : ℕ}
-- given
  (h₀ : y > 0)
  (h₁ : x ≤ y) :
-- imply
  x - 1 < y := by
-- proof
  apply Nat.lt_of_le_sub_one h₀
  apply Nat.le_of_succ_le_succ
  simp
  rwa [EqAddSub.of.Ge]

public theorem Nat.LtSub_1.of.Le.Gt_0.left
  {x y : ℕ}
-- given
  (h₀ : x > 0)
  (h₁ : x ≤ y) :
-- imply
  x - 1 < y :=
-- proof
  LtSub_1.of.Le.Gt_0 (Gt.of.Ge.Gt h₁ h₀) h₁

public theorem Nat.Gt_Sub_1.of.Ge.Gt_0
  {x y : ℕ}
-- given
  (h₀ : 0 < y)
  (h₁ : x ≤ y) :
-- imply
  y > x - 1 :=
-- proof
  LtSub_1.of.Le.Gt_0 h₀ h₁

public theorem Nat.Gt_Sub_1.of.Ge.Gt_0.left
  {x y : ℕ}
-- given
  (h₀ : 0 < x)
  (h₁ : x ≤ y) :
-- imply
  y > x - 1 :=
-- proof
  LtSub_1.of.Le.Gt_0.left h₀ h₁


-- created on 2025-05-03
-- updated on 2026-11-17
