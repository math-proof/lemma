import Lemma.Nat.EqAdd_0
import Lemma.Nat.GeAddS.of.Ge.Ge
open Nat


@[main]
private lemma main
  [AddZeroClass α]
  [Preorder α]
  [AddRightMono α]
  [AddLeftMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
-- imply
  a + b ≥ 0 := by
-- proof
  have h := GeAddS.of.Ge.Ge h₀ h₁
  simp only [EqAdd_0] at h
  exact h


-- created on 2024-11-25
-- updated on 2025-01-17
