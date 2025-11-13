import Lemma.Int.GtNeg_0.of.Lt_0
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Rat.Div_Neg.eq.NegDiv
import Lemma.Int.Le.of.GeNegS
open Rat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x < 0) :
-- imply
  a / x ≤ b / x := by
-- proof
  have := GtNeg_0.of.Lt_0 h₁
  have := GeDivS.of.Ge.Gt_0 h₀ this
  repeat rw [Div_Neg.eq.NegDiv] at this
  apply Le.of.GeNegS this


-- created on 2025-03-20
