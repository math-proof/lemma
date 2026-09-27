import Mathlib.Analysis.Calculus.Deriv.Mul
import sympy.dynamics.actor_critic
import sympy.Basic
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
  (a : ℝ) :
-- imply
  ForwardSolvesStateEquation δ Q θ (a • μ) := by
-- proof
  refine ⟨h₀.cont.const_smul a, fun t ht => ?_⟩
  refine ((h₀.hasDeriv t ht).const_smul a).congr_deriv ?_
  simp [Matrix.smul_vecMul, smul_comm a δ⁻¹]


-- created on 2026-09-26
