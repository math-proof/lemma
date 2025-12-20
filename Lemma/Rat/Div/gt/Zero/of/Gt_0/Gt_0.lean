import Lemma.Rat.GtInv_0.is.Gt_0
import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y > 0) :
-- imply
  x / y > 0 := by
-- proof
  have h₁ := GtInv_0.of.Gt_0 h₁
  have := Lt0Mul.of.Gt_0.Gt_0 h₀ h₁
  rwa [Mul_Inv.eq.Div] at this


-- created on 2025-07-20
