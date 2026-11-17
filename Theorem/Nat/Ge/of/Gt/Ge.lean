module

public import Theorem.Nat.Ge.of.Ge.Ge
public import Theorem.Nat.Ge.of.Gt

public section

open Nat


public theorem Nat.Ge.of.Gt.Ge
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : b > c) :
-- imply
  a ≥ c := by
-- proof
  apply Ge.of.Ge.Ge h₀
  apply Ge.of.Gt h₁


-- created on 2025-06-20
