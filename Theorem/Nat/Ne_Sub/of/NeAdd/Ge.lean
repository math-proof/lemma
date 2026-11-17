module

public import Theorem.Nat.EqAdd_Sub.of.Ge

public section

open Nat


@[comm 2]
public theorem left
  {x a b : ℕ}
-- given
  (h₀ : a ≥ b)
  (h₁ : b + x ≠ a) :
-- imply
  x ≠ a - b := by
-- proof
  by_contra h'
  rw [h'] at h₁
  rw [EqAdd_Sub.of.Ge (by assumption)] at h₁
  contradiction


@[comm 2]
public theorem Nat.Ne_Sub.of.NeAdd.Ge
  {x a b : ℕ}
-- given
  (h₀ : a ≥ b)
  (h₁ : x + b ≠ a) :
-- imply
  x ≠ a - b := by
-- proof
  by_contra h'
  rw [h'] at h₁
  rw [EqAddSub.of.Ge (by assumption)] at h₁
  contradiction


-- created on 2025-06-11
