module

public import Theorem.Nat.Lt.of.Lt.Le
public import Theorem.Nat.Le.of.Lt

public section

open Nat


public theorem Nat.Le.of.Le.Lt
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a < b)
  (h₁ : b ≤ c) :
-- imply
  a ≤ c := by
-- proof
  have := Lt.of.Lt.Le h₀ h₁
  apply Le.of.Lt this


public theorem relax
  {a b x : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : x < b) :
-- imply
  a ≤ b := by
-- proof
  exact le_trans h₀ h₁.le


public theorem Nat.Le.of.Le.Lt.subst
  {t x y b k : ℝ}
-- given
  (hk : k ≥ 0)
  (h₀ : y ≤ x * k + b)
  (h₁ : x < t) :
-- imply
  y ≤ t * k + b := by
-- proof
  nlinarith


-- created on 2019-11-24
-- updated on 2026-09-27
