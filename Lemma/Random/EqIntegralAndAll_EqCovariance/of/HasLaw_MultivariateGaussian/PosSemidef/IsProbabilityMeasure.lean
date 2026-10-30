import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Notation.Probability.HasLaw
import Syntax.Probability.JointRv.Part6
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory


/--
py `Random.EqIntegralAndAll_EqCovariance.of.HasLaw_MultivariateGaussian.PosSemidef.IsProbabilityMeasure`: if `x ∼[π] N(μ, σ)` (multivariate Gaussian),
then `μ = 𝔼[x]` and the square covariance matrix is `σ = cov[x]`.
-/
@[path]
private lemma main
  {n : ℕ} [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → EuclideanSpace ℝ (Fin n)} [PSpace π x]
  {μ : EuclideanSpace ℝ (Fin n)}
  {σ : Matrix (Fin n) (Fin n) ℝ}
-- given
  (_ : IsProbabilityMeasure π)
  (hσ : σ.PosSemidef)
  (h : x ∼[π] multivariateGaussian μ σ) :
-- imply
  μ = 𝔼[x: π](x) ∧
    σ = Matrix.of fun i j ↦ cov[fun ω ↦ x ω i, fun ω ↦ x ω j; π] := by
-- proof
  constructor
  ·
    symm
    simp only [Expectation.ofRV, Expectation.asRV_function]
    rw [h.map_eq]
    apply integral_id_multivariateGaussian
  ·
    apply Matrix.ext
    intro i j
    symm
    apply Eq.trans
    ·
      apply h.covariance_fun_comp
        (f := fun z : EuclideanSpace ℝ (Fin n) ↦ z i)
        (g := fun z : EuclideanSpace ℝ (Fin n) ↦ z j)
        (by fun_prop) (by fun_prop)
    ·
      apply covariance_eval_multivariateGaussian hσ


-- created on 2023-04-30
-- updated on 2026-10-29
