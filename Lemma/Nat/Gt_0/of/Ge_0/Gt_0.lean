import Lemma.Nat.EqAdd_0
import Lemma.Nat.LtAddS.of.Le.Lt
open Nat


@[main]
private lemma main
  [AddZeroClass α]
  [Preorder α]
  [AddLeftStrictMono α] [AddLeftMono α]
  [AddRightStrictMono α] [AddRightMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b > 0) :
-- imply
  a + b > 0 := by
-- proof
  have h₂ := LtAddS.of.Le.Lt h₀ h₁
  simp only [EqAdd_0] at h₂
  assumption


-- created on 2025-03-23
