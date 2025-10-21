import Lemma.Algebra.GeMulS.of.Ge.Gt_0
import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.GtInv_0.is.Gt_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Algebra Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y t : α}
-- given
  (h₀ : y ≥ t * x)
  (h₁ : x > 0) :
-- imply
  y / x ≥ t := by
-- proof
  have := GtInv_0.of.Gt_0 h₁
  have := GeMulS.of.Ge.Gt_0 h₀ this
  repeat rw [Mul_Inv.eq.Div] at this
  have h_Ne := Ne.of.Gt h₁
  rwa [EqDivMul.of.Ne_0 h_Ne] at this


-- created on 2025-03-30
