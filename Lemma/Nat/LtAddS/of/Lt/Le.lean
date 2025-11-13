import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.Lt.of.Lt.Le
open Nat


@[main, comm 3]
private lemma main
  [Add α]
  [Preorder α]
  [AddLeftStrictMono α] [AddLeftMono α]
  [AddRightStrictMono α] [AddRightMono α]
  {a b x y : α}
-- given
  (h₀ : a < b)
  (h₁ : x ≤ y) :
-- imply
  a + x < b + y := by
-- proof
  have h₂ := LtAddS.of.Lt x h₀
  have h₃ := LeAddS.of.Le.left b h₁
  apply Lt.of.Lt.Le h₂ h₃


-- created on 2025-01-17
-- updated on 2025-04-30
