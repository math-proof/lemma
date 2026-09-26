import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.Order.Group.PosPart
import sympy.stats.generator_matrix
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix
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
  (h₁ : ∀ t, 0 ≤ t → GeneratorMatrix (Q (θ t))) :
-- imply
  ∀ t, 0 ≤ t → ∑ i, μ t i = ∑ i, μ 0 i := by
-- proof
  intro T hT
  have hd : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (fun t => ∑ i, μ t i) 0 (Set.Ici t) t := by
    intro t ht
    have h := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ => hasDerivWithinAt_pi.1 (h₀.hasDeriv t ht.1) i
    refine h.congr_deriv ?_
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix (h₁ t ht.1), mul_zero]
  exact constant_of_has_deriv_right_zero (continuous_finsetSum _ fun i _ => (continuous_apply i).comp h₀.cont).continuousOn hd T ⟨hT, le_rfl⟩


-- created on 2026-09-26
