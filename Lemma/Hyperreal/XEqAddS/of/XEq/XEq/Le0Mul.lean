import Lemma.Hyperreal.Gt0Mul.of.Or_EqSt_Neg1.Infinite
import Lemma.Hyperreal.XEqAddS.of.XEq.XEq.NotAnd_Or_EqSt_Neg1
open Hyperreal


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h : b * y ≥ 0)
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a + x ≈ b + y := by
-- proof
  apply XEqAddS.of.XEq.XEq.NotAnd_Or_EqSt_Neg1 _ h₀ h₁
  contrapose! h
  apply Gt0Mul.of.Or_EqSt_Neg1.Infinite h.1 h.2


-- created on 2026-07-26
