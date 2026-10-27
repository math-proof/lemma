import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.HasLaw
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
py `Random.EqIntegralAndAll_EqCovariance.of.HasLaw_MultivariateGaussian.PosSemidef.IsProbabilityMeasure`: if `x ~ N(μ, Σ)` (multivariate Gaussian),
then the mean parameter is `𝔼[x]` and the covariance matrix entries are `Cov(xᵢ, xⱼ)`.
-/
@[path]
private lemma main
  {n : ℕ} [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → EuclideanSpace ℝ (Fin n)}
  {μ : EuclideanSpace ℝ (Fin n)}
  {S : Matrix (Fin n) (Fin n) ℝ}
-- given
  (_ : IsProbabilityMeasure π)
  (hS : S.PosSemidef)
  (h : HasLaw x (multivariateGaussian μ S) π) :
-- imply
  (∫ ω, x ω ∂π) = μ ∧
    ∀ i j : Fin n,
      covariance (fun ω ↦ x ω i) (fun ω ↦ x ω j) π = S i j := by
-- proof
  constructor
  ·
    apply Eq.trans
    ·
      apply h.integral_eq
    ·
      apply integral_id_multivariateGaussian
  ·
    intro i j
    apply Eq.trans
    ·
      apply h.covariance_fun_comp
        (f := fun z : EuclideanSpace ℝ (Fin n) ↦ z i)
        (g := fun z : EuclideanSpace ℝ (Fin n) ↦ z j)
        (by fun_prop) (by fun_prop)
    ·
      apply covariance_eval_multivariateGaussian hS


-- created on 2023-04-30
