import Lemma.Int.GtNeg_0.of.Lt_0
import Lemma.Rat.GtDivS.of.Gt.Gt_0
import Lemma.Rat.Div_Neg.eq.NegDiv
import Lemma.Int.Lt.of.GtNegS
open Rat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a > b)
  (h₁ : x < 0) :
-- imply
  a / x < b / x := by
-- proof
  have h₁ := GtNeg_0.of.Lt_0 h₁
  have := GtDivS.of.Gt.Gt_0 h₀ h₁
  repeat rw [Div_Neg.eq.NegDiv] at this
  exact Lt.of.GtNegS this


-- created on 2025-03-29
