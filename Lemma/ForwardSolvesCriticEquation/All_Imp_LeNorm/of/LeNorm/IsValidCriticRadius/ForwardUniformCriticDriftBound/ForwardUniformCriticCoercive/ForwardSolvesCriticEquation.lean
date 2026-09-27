import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.ForwardSolvesCriticEquation.All_LeSquareNormAddMulExpSquareNormMulDivSquareSSub1Exp.of.Gt_0.ForwardUniformCriticDriftBound.ForwardUniformCriticCoercive.ForwardSolvesCriticEquation
import Lemma.IsValidCriticRadius.CriticBallEntryTime.ge.ZeroAndMulExpMulNegCriticBallEntryTimeSquare.le.SubSquareDivSquareS.of.IsValidCriticRadius


@[main]
private lemma main
  {m : ℕ}
  {lambdaC : ℝ}
  {Bb : ℝ}
  {rW : ℝ}
  {M : ℝ}
  {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
  {b : ℝ → EuclideanVec m}
  {w : ℝ → EuclideanVec m}
-- given
  (h₀ : ForwardSolvesCriticEquation A b w)
  (h₁ : ForwardUniformCriticCoercive lambdaC A)
  (h₂ : ForwardUniformCriticDriftBound Bb b)
  (h₃ : IsValidCriticRadius lambdaC Bb rW)
  (h₄ : ‖w 0‖ ≤ M) :
-- imply
  ∀ t, critic_ball_entry_time lambdaC Bb rW M ≤ t → ‖w t‖ ≤ rW := by
-- proof
  intro t ht
  obtain ⟨hT, hspec⟩ := IsValidCriticRadius.CriticBallEntryTime.ge.ZeroAndMulExpMulNegCriticBallEntryTimeSquare.le.SubSquareDivSquareS.of.IsValidCriticRadius h₃
  have hl := h₃.lambdaC_pos
  have hE := ForwardSolvesCriticEquation.All_LeSquareNormAddMulExpSquareNormMulDivSquareSSub1Exp.of.Gt_0.ForwardUniformCriticDriftBound.ForwardUniformCriticCoercive.ForwardSolvesCriticEquation h₀ h₁ h₂ hl t (hT.trans ht)
  have hmono : Real.exp (-lambdaC * t) ≤ Real.exp (-lambdaC * critic_ball_entry_time lambdaC Bb rW M) := Real.exp_le_exp.2 (by nlinarith)
  have hM : ‖w 0‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₄ 2
  have hB0 : 0 ≤ Bb ^ 2 / lambdaC ^ 2 := by positivity
  have h6 : Real.exp (-lambdaC * t) * ‖w 0‖ ^ 2 ≤ Real.exp (-lambdaC * critic_ball_entry_time lambdaC Bb rW M) * M ^ 2 :=
    mul_le_mul hmono hM (sq_nonneg _) (Real.exp_pos _).le
  have h7 : Bb ^ 2 / lambdaC ^ 2 * (1 - Real.exp (-lambdaC * t)) ≤ Bb ^ 2 / lambdaC ^ 2 := by
    nlinarith [Real.exp_pos (-lambdaC * t)]
  have h8 : ‖w t‖ ^ 2 ≤ rW ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (zero_le_one.trans h₃.one_le) two_ne_zero).1 h8


-- created on 2026-09-26
