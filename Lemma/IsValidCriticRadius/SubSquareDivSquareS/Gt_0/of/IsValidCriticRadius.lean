import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {lambdaC : ℝ}
  {Bb : ℝ}
  {rW : ℝ}
-- given
  (h₀ : IsValidCriticRadius lambdaC Bb rW) :
-- imply
  0 < rW ^ 2 - Bb ^ 2 / lambdaC ^ 2 := by
-- proof
  have hq := div_nonneg h₀.Bb_nonneg h₀.lambdaC_pos.le
  have hr : Bb / lambdaC < rW := by linarith [h₀.one_le, h₀.ratio_le]
  have h := pow_lt_pow_left₀ hr hq two_ne_zero
  rw [div_pow] at h
  linarith


-- created on 2026-09-26
