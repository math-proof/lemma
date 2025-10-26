import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Int.GeMulS.of.Le.Lt_0
import Lemma.Rat.LtInv_0.is.Lt_0
import Lemma.Nat.Ne.of.Lt
open Nat Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y t : α}
-- given
  (h₀ : y ≤ t * x)
  (h₁ : x < 0) :
-- imply
  y / x ≥ t := by
-- proof
  have : x⁻¹ < 0 := LtInv_0.of.Lt_0 h₁
  have := GeMulS.of.Le.Lt_0 h₀ this
  rw [
    Mul_Inv.eq.Div,
    Mul_Inv.eq.Div
  ] at this
  have h_Ne := Ne.of.Lt h₁
  rwa [EqDivMul.of.Ne_0 h_Ne] at this


-- created on 2025-03-30
