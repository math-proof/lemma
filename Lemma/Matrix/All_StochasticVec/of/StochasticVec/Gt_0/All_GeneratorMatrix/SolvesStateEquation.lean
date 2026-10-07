import sympy.stats.generator_matrix
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.Matrix.All_StochasticVec.of.StochasticVec.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation
import Lemma.Matrix.ForwardSolvesStateEquation.of.SolvesStateEquation
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {d : ℕ}
  {δ : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : ℝ → EuclideanVec d}
  {μ : ℝ → S → ℝ}
-- given
  (h₀ : SolvesStateEquation δ Q θ μ)
  (h₁ : ∀ t, GeneratorMatrix (Q (θ t)))
  (h₂ : 0 < δ)
  (h₃ : StochasticVec (μ 0)) :
-- imply
  ∀ t, 0 ≤ t → StochasticVec (μ t) := by
-- proof
  exact Matrix.All_StochasticVec.of.StochasticVec.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation (Matrix.ForwardSolvesStateEquation.of.SolvesStateEquation h₀) (fun t _ => h₁ t) h₂ h₃


-- created on 2026-09-26
