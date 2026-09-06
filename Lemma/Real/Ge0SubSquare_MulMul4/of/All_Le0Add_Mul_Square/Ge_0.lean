import Lemma.Rat.Ge0SubSquare_MulMul4.of.All_Le0Add_Mul_Square.Gt_0
import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Rat.EqMul_Div.of.Ne_0
open Rat Nat


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a ≥ 0)
  (h₁ : ∀ x : ℝ, c + b * x + a * x² ≥ 0) :
-- imply
  b² - 4 * a * c ≤ 0 := by
-- proof
  if h : a = 0 then
    rw [h] at h₁
    norm_num at h₁
    rw [h]
    norm_num
    by_contra h
    have : ∃ t, b * t + c < 0 := by
      use -(c + 1) / b
      rw [EqMul_Div.of.Ne_0 h]
      simp
    let ⟨t, h_t⟩ := this
    have := h₁ t
    linarith
  else
    have := Gt.of.Ge.Ne h₀ h
    apply Ge0SubSquare_MulMul4.of.All_Le0Add_Mul_Square.Gt_0 this h₁


-- created on 2025-04-06
-- updated on 2026-09-06
