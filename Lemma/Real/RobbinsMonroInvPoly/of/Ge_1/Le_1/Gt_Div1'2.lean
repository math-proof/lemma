import sympy.stats.step_size
import Lemma.Real.TendstoSumPow.of.Ge_1.Le_1
import Lemma.Real.SummableSquarePow.of.Gt_Div1'2
open Real


@[main]
private lemma main
  {ν : ℝ}
  {n₀ : ℕ}
-- given
  (h₀ : 1 / 2 < ν)
  (h₁ : ν ≤ 1)
  (h₂ : 1 ≤ n₀) :
-- imply
  RobbinsMonro fun n : ℕ => inv_poly ν n₀ n := by
-- proof
  have hn₀ : (1 : ℝ) ≤ n₀ := by exact_mod_cast h₂
  exact ⟨fun n => Real.rpow_pos_of_pos (by positivity) _, TendstoSumPow.of.Ge_1.Le_1 h₁ h₂, SummableSquarePow.of.Gt_Div1'2 h₀⟩


-- created on 2026-09-26