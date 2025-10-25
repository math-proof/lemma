import Lemma.Int.GtNeg_0.of.Lt_0
import Lemma.Algebra.Div_Neg.eq.NegDiv
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Int.Ge.of.LeNegS
open Algebra Rat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x < 0) :
-- imply
  a / x ≥ b / x := by
-- proof
  have := GtNeg_0.of.Lt_0 h₁
  have := LeDivS.of.Le.Gt_0 h₀ this
  repeat rw [Div_Neg.eq.NegDiv] at this
  exact Ge.of.LeNegS this


-- created on 2025-03-29
