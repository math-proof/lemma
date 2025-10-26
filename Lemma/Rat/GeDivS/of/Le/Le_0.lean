import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Rat.LeInv_0.is.Le_0
import Lemma.Int.GeMulS.of.Le.Le_0
open Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≤ 0) :
-- imply
  a / x ≥ b / x := by
-- proof
  have := LeInv_0.of.Le_0 h₁
  have := GeMulS.of.Le.Le_0 h₀ this
  repeat rw [Mul_Inv.eq.Div] at this
  assumption


-- created on 2025-03-30
