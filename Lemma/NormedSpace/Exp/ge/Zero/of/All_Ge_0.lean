import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Order
import sympy.stats.generator_matrix
import sympy.Basic
open Matrix NormedSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {M : Matrix S S ℝ}
-- given
  (h₀ : ∀ i j, 0 ≤ M i j)
  (i j : S) :
-- imply
  0 ≤ exp M i j := by
-- proof
  let _ : NormedRing (Matrix S S ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix S S ℝ) := Matrix.linftyOpNormedAlgebra
  have hpow : ∀ n : ℕ, ∀ i j, 0 ≤ (M ^ n) i j := by
    intro n
    induction n with
    | zero =>
      intro i j
      by_cases h : i = j <;> simp [h]
    | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (h₀ k j)
  let E := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j : Matrix S S ℝ →ₗ[ℝ] ℝ)
  have he : exp M i j = ∑' n : ℕ, E (((n.factorial : ℝ)⁻¹) • M ^ n) := by
    rw [← E.map_tsum (expSeries_summable' (𝕂 := ℝ) M), ← congrFun (exp_eq_tsum ℝ) M]
    rfl
  rw [he]
  refine tsum_nonneg fun n => ?_
  simp only [E, LinearMap.coe_toContinuousLinearMap', Matrix.entryLinearMap_apply, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (hpow n i j)


-- created on 2026-09-26
