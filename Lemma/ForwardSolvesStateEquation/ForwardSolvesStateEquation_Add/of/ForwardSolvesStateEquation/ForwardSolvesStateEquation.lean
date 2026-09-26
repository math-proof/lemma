import Mathlib.Analysis.Calculus.Deriv.Add
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
  {ν : ℝ → S → ℝ}
-- given
  (h₀ : ForwardSolvesStateEquation δ Q θ μ)
  (h₁ : ForwardSolvesStateEquation δ Q θ ν) :
-- imply
  ForwardSolvesStateEquation δ Q θ (μ + ν) := by
-- proof
  refine ⟨h₀.cont.add h₁.cont, fun t ht => ?_⟩
  refine ((h₀.hasDeriv t ht).add (h₁.hasDeriv t ht)).congr_deriv ?_
  simp [Matrix.add_vecMul, smul_add]


-- created on 2026-09-26
