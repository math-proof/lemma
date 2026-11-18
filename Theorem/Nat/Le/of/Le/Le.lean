module

public import Mathlib

public section


public theorem Nat.Le.of.Le.Le
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : b ≤ c) :
-- imply
  a ≤ c :=
-- proof
  le_trans h₀ h₁


public theorem Nat.Le.of.Le.Le.subst
  {y b x t k : ℝ}
-- given
  (h₀ : y ≤ x * k + b)
  (h₁ : x ≤ t)
  (h₂ : k > 0) :
-- imply
  y ≤ t * k + b := by
-- proof
  nlinarith


-- created on 2018-02-26
-- updated on 2026-10-26
