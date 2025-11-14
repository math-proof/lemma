import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.Lt.of.Lt.Lt
open Nat


@[main, comm 3]
private lemma main
  [Add α]
  [Preorder α]
  [AddRightStrictMono α] [AddLeftStrictMono α]
  {a b x y : α}
-- given
  (h₀ : a < b)
  (h₁ : x < y) :
-- imply
  a + x < b + y := by
-- proof
  have h₂ := LtAddS.of.Lt x h₀
  have h₃ := LtAddS.of.Lt.left b h₁
  apply Lt.of.Lt.Lt h₂ h₃


-- created on 2024-11-25
-- updated on 2025-04-04
