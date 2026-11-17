module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


@[comm 1]
public theorem Nat.LeMulS.of.Ge_0.Le
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : a ≤ b) :
-- imply
  x * a ≤ x * b := by
-- proof
  exact mul_le_mul_of_nonneg_left h₁ h₀


-- created on 2018-06-17
-- updated on 2026-10-26
