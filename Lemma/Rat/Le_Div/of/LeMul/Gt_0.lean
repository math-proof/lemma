import Lemma.Nat.LeMulS.of.Le.Gt_0
import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Rat.GtInv_0.is.Gt_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Nat Rat


@[main, comm 2]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y t : α}
-- given
  (h₀ : t * x ≤ y)
  (h₁ : x > 0) :
-- imply
  t ≤ y / x := by
-- proof
  have := GtInv_0.of.Gt_0 h₁
  have := LeMulS.of.Le.Gt_0 h₀ this
  repeat rw [Mul_Inv.eq.Div] at this
  have h_Ne := Ne.of.Gt h₁
  rwa [EqDivMul.of.Ne_0 h_Ne] at this


-- created on 2025-03-30
