import sympy.stats.generator_matrix
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.SolvesStateEquation.All_StochasticVec.of.StochasticVec.Gt_0.All_GeneratorMatrix.SolvesStateEquation
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {d : ℕ}
  {δ : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {μ : ℝ → S → ℝ}
  {θ₀ : EuclideanVec d}
-- given
  (h₀ : ∀ θ, GeneratorMatrix (Q θ))
  (h₁ : 0 < δ)
  (h₂ : SolvesStateEquation δ Q (fun _ => θ₀) μ)
  (h₃ : StochasticVec (μ 0)) :
-- imply
  ∀ t, 0 ≤ t → StochasticVec (μ t) := by
-- proof
  exact SolvesStateEquation.All_StochasticVec.of.StochasticVec.Gt_0.All_GeneratorMatrix.SolvesStateEquation h₂ (fun _ => h₀ θ₀) h₁ h₃


-- created on 2026-09-26
