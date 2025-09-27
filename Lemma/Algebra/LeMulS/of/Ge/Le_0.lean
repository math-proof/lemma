import Lemma.Algebra.GeMulS.of.Ge.Ge_0
import Lemma.Algebra.GeNeg_0.of.Le_0
import Lemma.Algebra.Mul_Neg.eq.NegMul
import Lemma.Algebra.Le.of.GeNegS
open Algebra


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x ≤ 0) :
-- imply
  a * x ≤ b * x := by
-- proof
  have := GeNeg_0.of.Le_0 h₁
  have := GeMulS.of.Ge.Ge_0 h₀ this
  repeat rw [Mul_Neg.eq.NegMul] at this
  apply Le.of.GeNegS this


-- created on 2025-03-23
-- updated on 2025-03-30
