module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Nat.EqSubAdd
public import Theorem.Nat.MinAddS.eq.AddMin

public section

open Nat


@[comm]
public theorem Nat.MinSubS.eq.SubMin.of.Ge.Ge
  {a b c : ℕ}
-- given
  (h₀ : a ≥ c)
  (h₁ : b ≥ c) :
-- imply
  (a - c) ⊓ (b - c) = a ⊓ b - c := by
-- proof
  let a' := a - c
  let b' := b - c
  have h_a : a = a' + c := by
    simp [a', h₀]
  have h_b : b = b' + c := by
    simp [b', h₁]
  rw [h_a, h_b]
  rw [MinAddS.eq.AddMin]
  repeat rw [EqSubAdd]


public theorem Nat.SubMin.eq.MinSubS.of.Ge.Ge
  {a b c : ℕ}
  (h₀ : a ≥ c)
  (h₁ : b ≥ c) :
  a ⊓ b - c = (a - c) ⊓ (b - c) :=
  (Nat.MinSubS.eq.SubMin.of.Ge.Ge h₀ h₁).symm


-- created on 2025-06-20
