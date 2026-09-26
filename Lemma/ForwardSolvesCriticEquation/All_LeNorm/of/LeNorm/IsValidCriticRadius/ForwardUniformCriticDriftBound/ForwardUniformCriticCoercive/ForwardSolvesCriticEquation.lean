import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.ForwardSolvesCriticEquation.All_LeSquareNormAddMulExpSquareNormMulDivSquareSSub1Exp.of.Gt_0.ForwardUniformCriticDriftBound.ForwardUniformCriticCoercive.ForwardSolvesCriticEquation
import Lemma.IsValidCriticRadius.DivSquareS.le.Square.of.IsValidCriticRadius


@[main]
private lemma main
  {m : ℕ}
  {lambdaC : ℝ}
  {Bb : ℝ}
  {rW : ℝ}
  {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
  {b : ℝ → EuclideanVec m}
  {w : ℝ → EuclideanVec m}
-- given
  (h₀ : ForwardSolvesCriticEquation A b w)
  (h₁ : ForwardUniformCriticCoercive lambdaC A)
  (h₂ : ForwardUniformCriticDriftBound Bb b)
  (h₃ : IsValidCriticRadius lambdaC Bb rW)
  (h₄ : ‖w 0‖ ≤ rW) :
-- imply
  ∀ t, 0 ≤ t → ‖w t‖ ≤ rW := by
-- proof
  intro t ht
  have hE := ForwardSolvesCriticEquation.All_LeSquareNormAddMulExpSquareNormMulDivSquareSSub1Exp.of.Gt_0.ForwardUniformCriticDriftBound.ForwardUniformCriticCoercive.ForwardSolvesCriticEquation h₀ h₁ h₂ h₃.lambdaC_pos t ht
  have hB := IsValidCriticRadius.DivSquareS.le.Square.of.IsValidCriticRadius h₃
  have hr : 0 ≤ rW := zero_le_one.trans h₃.one_le
  have he := Real.exp_pos (-lambdaC * t)
  have he1 : Real.exp (-lambdaC * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [h₃.lambdaC_pos])
  have h0 : ‖w 0‖ ^ 2 ≤ rW ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₄ 2
  have h5 := mul_le_mul_of_nonneg_left h0 he.le
  have h6 := mul_le_mul_of_nonneg_right hB (sub_nonneg.2 he1)
  have h7 : ‖w t‖ ^ 2 ≤ rW ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).1 h7


-- created on 2026-09-26
