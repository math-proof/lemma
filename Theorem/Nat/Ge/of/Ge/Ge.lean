module

public import Mathlib

public section


public theorem Nat.Ge.of.Ge.Ge
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : b ≥ c) :
-- imply
  a ≥ c :=
-- proof
  ge_trans h₀ h₁


public theorem Nat.Ge.of.Ge.Ge.subst
  {y b x t k : ℝ}
-- given
  (hk : k > 0)
  (h₀ : y ≥ x * k + b)
  (h₁ : x ≥ t) :
-- imply
  y ≥ t * k + b := by
-- proof
  nlinarith


-- created on 2018-03-12
-- updated on 2026-10-26
