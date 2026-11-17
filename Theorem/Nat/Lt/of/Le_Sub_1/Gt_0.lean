module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


@[comm 2]
public theorem Nat.Lt.of.Le_Sub_1.Gt_0
  {x y : ℕ}
-- given
  (h₀ : y > 0)
  (h₁ : x ≤ y - 1) :
-- imply
  x < y := by
-- proof
  rwa [Nat.le_sub_one_iff_lt h₀] at h₁


-- created on 2025-05-07
