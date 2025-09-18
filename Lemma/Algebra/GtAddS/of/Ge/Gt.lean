import Lemma.Algebra.GeAddS.is.Ge
import Lemma.Algebra.GtAddS.is.Gt
import Lemma.Algebra.Gt.of.Ge.Gt
open Algebra


@[main]
private lemma main
  [Add α]
  [Preorder α]
  [AddLeftStrictMono α] [AddLeftMono α]
  [AddRightStrictMono α] [AddRightMono α]
  {a b x y : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x > y) :
-- imply
  a + x > b + y := by
-- proof
  have h₂ := GeAddS.of.Ge x h₀
  have h₃ := GtAddS.of.Gt.left b h₁
  apply Gt.of.Ge.Gt h₂ h₃


-- created on 2025-01-17
-- updated on 2025-04-30
