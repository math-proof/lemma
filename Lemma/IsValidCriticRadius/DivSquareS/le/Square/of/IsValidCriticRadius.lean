import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.IsValidCriticRadius.SubSquareDivSquareS.Gt_0.of.IsValidCriticRadius


@[main]
private lemma main
  {lambdaC : ℝ}
  {Bb : ℝ}
  {rW : ℝ}
-- given
  (h₀ : IsValidCriticRadius lambdaC Bb rW) :
-- imply
  Bb ^ 2 / lambdaC ^ 2 ≤ rW ^ 2 := by
-- proof
  linarith [IsValidCriticRadius.SubSquareDivSquareS.Gt_0.of.IsValidCriticRadius h₀]


-- created on 2026-09-26
