import Lemma.Hyperreal.XEqAddS.of.XEq.XEq.NotAnd_EqSt_Neg1
import Lemma.Hyperreal.XEqNegS.of.XEq
import Lemma.Hyperreal.StNeg.eq.NegSt
import Lemma.Rat.Div_Neg.eq.NegDiv
open Hyperreal Rat


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h_and : ¬((b → ∞) ∧ stdPart (b / y) = 1))
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a - x ≈ b - y := by
-- proof
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply @XEqAddS.of.XEq.XEq.NotAnd_EqSt_Neg1 (x := -x) (y := -y)
  ·
    intro ⟨h_b, h_st⟩
    rw [Div_Neg.eq.NegDiv, StNeg.eq.NegSt] at h_st
    have h_st1 : stdPart (b / y) = 1 := by simpa using h_st
    exact h_and ⟨h_b, h_st1⟩
  ·
    exact h₀
  ·
    exact XEqNegS.of.XEq h₁


-- created on 2026-07-26
