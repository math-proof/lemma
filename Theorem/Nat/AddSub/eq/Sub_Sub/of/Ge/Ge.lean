module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Nat.EqSubAdd
public import Theorem.Nat.Sub_Add.eq.SubSub
public import Theorem.Nat.EqAddSub.of.Ge
public import Theorem.Nat.Le_Sub.of.LeAdd

public section

open Nat


@[comm]
public theorem Nat.AddSub.eq.Sub_Sub.of.Ge.Ge
  {a b c : ℕ}
-- given
  (h₀ : a ≥ b)
  (h₁ : b ≥ c) :
-- imply
  a - b + c = a - (b - c) := by
-- proof
  let d := b - c
  have h_b : b = d + c := by
    simp [d, h₁]
  rw [h_b] at h₀ ⊢
  rw [EqSubAdd]
  rw [Sub_Add.eq.SubSub]
  rw [EqAddSub.of.Ge]
  apply GeSub.of.Ge_Add.left h₀


-- created on 2025-06-18
-- updated on 2025-06-20
