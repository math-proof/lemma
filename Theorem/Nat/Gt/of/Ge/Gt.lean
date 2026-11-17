module

public import Mathlib.Order.Basic

set_option linter.dupNamespace false

public section

public theorem Nat.Gt.of.Ge.Gt
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : b > c) :
-- imply
  a > c :=
-- proof
  lt_of_le_of_lt' h₀ h₁


-- created on 2018-03-13
-- updated on 2026-11-17
