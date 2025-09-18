import Lemma.Algebra.GtAddS.is.Gt
import Lemma.Algebra.Gt.of.Gt.Gt
open Algebra


@[main]
private lemma main
  [Add α]
  [Preorder α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  {a b x y : α}
-- given
  (h₀ : a > b)
  (h₁ : x > y) :
-- imply
  a + x > b + y := by
-- proof
  have h₂ := GtAddS.of.Gt x h₀
  have h₃ := GtAddS.of.Gt.left b h₁
  apply Gt.of.Gt.Gt h₂ h₃


-- created on 2024-11-25
-- updated on 2025-04-30
