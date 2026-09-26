import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.IsValidCriticRadius.SubSquareDivSquareS.Gt_0.of.IsValidCriticRadius


@[main]
private lemma main
  {lambdaC : ℝ}
  {Bb : ℝ}
  {rW : ℝ}
  {M : ℝ}
-- given
  (h₀ : IsValidCriticRadius lambdaC Bb rW) :
-- imply
  0 ≤ critic_ball_entry_time lambdaC Bb rW M ∧ Real.exp (-lambdaC * critic_ball_entry_time lambdaC Bb rW M) * M ^ 2 ≤ rW ^ 2 - Bb ^ 2 / lambdaC ^ 2 := by
-- proof
  have hD := IsValidCriticRadius.SubSquareDivSquareS.Gt_0.of.IsValidCriticRadius h₀
  have hl := h₀.lambdaC_pos
  simp only [critic_ball_entry_time]
  set D := rW ^ 2 - Bb ^ 2 / lambdaC ^ 2
  have h1 : 1 ≤ 1 + M ^ 2 / D := by
    have := div_nonneg (sq_nonneg M) hD.le
    linarith
  refine ⟨div_nonneg (Real.log_nonneg h1) hl.le, ?_⟩
  have e : -lambdaC * (Real.log (1 + M ^ 2 / D) / lambdaC) = -Real.log (1 + M ^ 2 / D) := by
    field_simp
  rw [e, Real.exp_neg, Real.exp_log (by linarith), inv_mul_le_iff₀ (by linarith), add_mul, one_mul, div_mul_cancel₀ _ hD.ne']
  linarith


-- created on 2026-09-26
