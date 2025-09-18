import Lemma.Algebra.LtAddS.of.Lt.Lt
import Lemma.Algebra.Lt.of.Le.Lt
import Lemma.Algebra.LeMulS.of.Ge_0.Lt
import Lemma.Algebra.LtMulS.of.Lt.Gt_0
import Lemma.Set.LtSquareS.of.In_Ico0
open Algebra Set


/--
Given two real numbers \( x_0 \) and \( x_1 \) within the interval \([0, \frac{1}{2})\), the sum of their squares plus their product is strictly less than \(\frac{3}{4}\).
This result leverages the strict monotonicity of addition and multiplication under non-negative constraints to establish the upper bound.
-/
@[main]
private lemma main
  {x₀ x₁ : ℝ}
-- given
  (h₀ : x₀ ∈ Ico 0 (1 / 2))
  (h₁ : x₁ ∈ Ico 0 (1 / 2)) :
-- imply
  x₀² + x₁² + x₀ * x₁ < 3 / 4 := by
-- proof
  have ⟨h_Ge, h_Ltx0⟩ := h₀
  have ⟨_, h_Ltx1⟩ := h₁
  have h₀ := LtSquareS.of.In_Ico0 h₀
  norm_num at h₀
  have h₁ := LtSquareS.of.In_Ico0 h₁
  norm_num at h₁
  have h_Ltx0 := LtMulS.of.Lt.Gt_0 h_Ltx0 (by norm_num : (1 : ℝ) / 2 > 0)
  norm_num at h_Ltx0
  have := LeMulS.of.Ge_0.Lt h_Ge h_Ltx1
  have h₂ := Lt.of.Le.Lt this h_Ltx0
  have := LtAddS.of.Lt.Lt h₀ h₁
  have := LtAddS.of.Lt.Lt this h₂
  norm_num at this
  assumption


-- created on 2025-03-24
-- updated on 2025-04-05
