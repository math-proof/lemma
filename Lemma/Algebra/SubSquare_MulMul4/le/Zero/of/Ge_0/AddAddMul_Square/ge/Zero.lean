import sympy.core.power
import Lemma.Algebra.SubSquare_MulMul4.le.Zero.of.Gt_0.AddAddMul_Square.ge.Zero
import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Algebra.EqMul_Div.of.Ne_0
open Algebra


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : ∀ x : ℝ, a * x² + b * x + c ≥ 0)
  (h₁ : a ≥ 0) :
-- imply
  b² - 4 * a * c ≤ 0 := by
-- proof
  by_cases h : a = 0
  ·
    rw [h] at h₀
    norm_num at h₀
    rw [h]
    norm_num
    -- b * x + c ≥ 0 for all x
    -- so that b * 1 + c = b + c ≥ 0 b >= -c
    -- so that b * (-1) + c = -b + c ≥ 0 => b <=c
    -- so that b * 0 + c = -b + c ≥ 0 => c >= 0
    -- if b ≠ 0, then b * (-(c + 1) / b) + c = -1 < 0, contrary to b * x + c ≥ 0 for all x
    -- This implies b = 0 (otherwise, the inequality would fail for large x).
    -- Then, the discriminant becomes 0² - 4 * 0 * c = 0 ≤ 0.
    by_contra h
    have : ∃ t, b * t + c < 0 := by
      use -(c + 1) / b
      rw [EqMul_Div.of.Ne_0 h]
      simp
    let ⟨t, h_t⟩ := this
    have := h₀ t
    linarith
  ·
    have := Gt.of.Ge.Ne h₁ h
    apply SubSquare_MulMul4.le.Zero.of.Gt_0.AddAddMul_Square.ge.Zero this h₀


-- created on 2025-04-06
