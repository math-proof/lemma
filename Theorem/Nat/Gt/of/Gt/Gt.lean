module

public import Mathlib

public section


public theorem Nat.Gt.of.Gt.Gt
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b > c) :
-- imply
  a > c :=
-- proof
  gt_trans h₀ h₁


public theorem Nat.Gt.of.Gt.Gt.subst
  {y b x t k : ℝ}
-- given
  (hk : k > 0)
  (h₀ : y > x * k + b)
  (h₁ : x > t) :
-- imply
  y > t * k + b := by
-- proof
  nlinarith


-- created on 2018-05-19
-- updated on 2026-10-26
