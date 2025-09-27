import Lemma.Algebra.GtNeg_0.of.Lt_0
import Lemma.Algebra.GtDivS.of.Gt.Gt_0
import Lemma.Algebra.Div_Neg.eq.NegDiv
import Lemma.Algebra.Lt.of.GtNegS
open Algebra


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
