import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Rat.LtInv_0.is.Lt_0
import Lemma.Int.Mul.lt.Zero.of.Gt_0.Lt_0
open Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y < 0) :
-- imply
  x / y < 0 := by
-- proof
  have h₁ := LtInv_0.of.Lt_0 h₁
  have := Mul.lt.Zero.of.Gt_0.Lt_0 h₀ h₁
  rwa [Mul_Inv.eq.Div] at this


-- created on 2025-07-20
