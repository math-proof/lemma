import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.Le.of.Le.Le
open Nat


@[main]
private lemma main
  [Add α]
  [Preorder α]
  [AddRightMono α]
  [AddLeftMono α]
  {a b x y : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≤ y) :
-- imply
  a + x ≤ b + y := by
-- proof
  have h₂ := LeAddS.of.Le x h₀
  have h₃ := LeAddS.of.Le.left b h₁
  apply Le.of.Le.Le h₂ h₃


-- created on 2024-11-25
-- updated on 2025-04-30
