import Lemma.Hyperreal.XEqAddS.of.XEq.XEq.NotAnd_Or_EqSt_Neg1
import Lemma.Hyperreal.XEqNegS.of.XEq
import Lemma.Hyperreal.StNeg.eq.NegSt
import Lemma.Rat.Div_Neg.eq.NegDiv
open Hyperreal Rat


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h_or : ¬((b → ∞) ∧ (b = y ∨ stdPart (b / y) = 1)))
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a - x ≈ b - y := by
-- proof
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply XEqAddS.of.XEq.XEq.NotAnd_Or_EqSt_Neg1
  ·
    intro h_bad
    obtain ⟨h_b, h_or'⟩ := h_bad
    obtain h_sum | h_st := h_or'
    ·
      exact h_or ⟨h_b, Or.inl (by aesop)⟩
    ·
      rw [Div_Neg.eq.NegDiv, StNeg.eq.NegSt] at h_st
      exact h_or ⟨h_b, Or.inr (by aesop)⟩
  ·
    exact h₀
  ·
    exact XEqNegS.of.XEq h₁


-- created on 2026-07-26
