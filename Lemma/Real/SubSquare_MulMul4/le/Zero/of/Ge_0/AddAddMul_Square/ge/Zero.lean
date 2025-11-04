import sympy.core.power
import Lemma.Rat.SubSquare_MulMul4.le.Zero.of.Gt_0.AddAddMul_Square.ge.Zero
import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Rat.EqMul_Div.of.Ne_0
open Rat Nat


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : ∀ x : ℝ, a * x² + b * x + c ≥ 0)
  (h₁ : a ≥ 0) :
-- imply
  b² - 4 * a * c ≤ 0 := by
-- proof
  if h : a = 0 then
    rw [h] at h₀
    norm_num at h₀
    rw [h]
    norm_num
    by_contra h
    have : ∃ t, b * t + c < 0 := by
      use -(c + 1) / b
      rw [EqMul_Div.of.Ne_0 h]
      simp
    let ⟨t, h_t⟩ := this
    have := h₀ t
    linarith
  else
    have := Gt.of.Ge.Ne h₁ h
    apply SubSquare_MulMul4.le.Zero.of.Gt_0.AddAddMul_Square.ge.Zero this h₀


-- created on 2025-04-06
