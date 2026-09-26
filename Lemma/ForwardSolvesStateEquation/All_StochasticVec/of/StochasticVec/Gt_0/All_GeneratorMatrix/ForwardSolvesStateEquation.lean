import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.Order.Group.PosPart
import sympy.stats.generator_matrix
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.ForwardSolvesStateEquation.All_All_Ge_0.of.All_Ge_0.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation
import Lemma.ForwardSolvesStateEquation.All_EqSumSum.of.All_GeneratorMatrix.ForwardSolvesStateEquation
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
  (h₀ : ForwardSolvesStateEquation δ Q θ μ)
  (h₁ : ∀ t, 0 ≤ t → GeneratorMatrix (Q (θ t)))
  (h₂ : 0 < δ)
  (h₃ : StochasticVec (μ 0)) :
-- imply
  ∀ t, 0 ≤ t → StochasticVec (μ t) := by
-- proof
  exact fun t ht => ⟨ForwardSolvesStateEquation.All_All_Ge_0.of.All_Ge_0.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation h₀ h₁ h₂ h₃.nonneg t ht, (ForwardSolvesStateEquation.All_EqSumSum.of.All_GeneratorMatrix.ForwardSolvesStateEquation h₀ h₁ t ht).trans h₃.rowsum⟩


-- created on 2026-09-26
