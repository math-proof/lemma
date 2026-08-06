import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.Gt0Mul.of.Or_EqSt_Neg1.Infinite
import Lemma.Hyperreal.InfiniteDiv.of.Infinite.NotInfinite
import Lemma.Hyperreal.XEqAddS.of.XEq.XEq.NotAnd_EqSt_Neg1
open Hyperreal


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h : b * y ≥ 0 ∨ ¬(b → ∞) ∨ ¬(y → ∞))
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a + x ≈ b + y := by
-- proof
  apply XEqAddS.of.XEq.XEq.NotAnd_EqSt_Neg1 _ h₀ h₁
  intro ⟨h_b, h_st⟩
  obtain h_mul | h_b_fin | h_y_fin := h
  ·
    have h_by := Gt0Mul.of.Or_EqSt_Neg1.Infinite h_b (Or.inr h_st)
    linarith
  ·
    exact h_b_fin h_b
  ·
    if h_y0 : y = 0 then
      rw [h_y0] at h_st
      norm_num at h_st
    else
      have _ : NeZero y := ⟨h_y0⟩
      have h_y : y → ∞ := by
        by_contra h_y_nf
        have h_div := InfiniteDiv.of.Infinite.NotInfinite h_b h_y_nf
        rw [EqSt_0.of.Infinite h_div] at h_st
        norm_num at h_st
      exact h_y_fin h_y


-- created on 2026-07-26
