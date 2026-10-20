/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ClassicalOrthogonalPolynomial.lean -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace MetaMathlibExt

/-- Classical orthogonal polynomial family (concept `jis_sem_6573fe45e3bbd4f163aed756`,
    source block `jis_srcblock_e90c95146a5fe658`, lines 208-221): a sequence `P n` of monic
    degree-`n` real polynomials, orthogonal for distinct indices with respect to a measure `μ`
    with nonzero squared norms, where `μ` is absolutely continuous with nonnegative weight
    density `w`
    against restricted Lebesgue volume, and `w` satisfies `w'/w = U/V` with
    `U x = u₀ + u₁ * x` and `V x = v₀ + v₁ * x + v₂ * x ^ 2`. -/
structure ClassicalOrthogonalPolynomialFamily where
  /-- Sequence of real polynomials (concept `jis_sem_6573fe45e3bbd4f163aed756`). -/
  P : ℕ → Polynomial ℝ
  /-- The source uses the monic normalization of the polynomial family. -/
  monic : ∀ n : ℕ, (P n).Monic
  /-- The `n`th member has degree exactly `n`. -/
  natDegree_eq : ∀ n : ℕ, (P n).natDegree = n
  /-- Orthogonalizing measure (concept `jis_sem_6573fe45e3bbd4f163aed756`). -/
  μ : MeasureTheory.Measure ℝ
  /-- Supporting domain for the weight density (source block `jis_srcblock_e90c95146a5fe658`). -/
  domain : Set ℝ
  /-- The domain is measurable (source block `jis_srcblock_e90c95146a5fe658`). -/
  measurable_domain : MeasurableSet domain
  /-- The support domain is an interval, as in the classical families. -/
  ordConnected_domain : Set.OrdConnected domain
  /-- The support interval has nonempty interior, so the Pearson equation is not vacuous. -/
  interior_domain_nonempty : (interior domain).Nonempty
  /-- Distinct members are orthogonal with respect to `μ`
      (concept `jis_sem_6573fe45e3bbd4f163aed756`). -/
  orthogonal : ∀ m n : ℕ, m ≠ n →
    MeasureTheory.integral μ (fun x => Polynomial.eval x (P m) * Polynomial.eval x (P n)) = 0
  /-- Each squared norm is nonzero, excluding the zero family
      (concept `jis_sem_6573fe45e3bbd4f163aed756`). -/
  norm_ne_zero : ∀ n : ℕ,
    MeasureTheory.integral μ (fun x => (Polynomial.eval x (P n)) ^ 2) ≠ 0
  /-- Nonnegative weight function (source block `jis_srcblock_e90c95146a5fe658`). -/
  weight : ℝ → ℝ
  /-- The weight is nonnegative (source block `jis_srcblock_e90c95146a5fe658`). -/
  weight_nonneg : ∀ x ∈ domain, 0 ≤ weight x
  /-- The measure is the weight density against restricted Lebesgue volume
      (source block `jis_srcblock_e90c95146a5fe658`). -/
  measure_eq : μ = (MeasureTheory.volume.restrict domain).withDensity
    (fun x => ENNReal.ofReal (weight x))
  /-- Classical Pearson equation `V w' = U w`, where `U` is linear and `V` is a genuinely
      nonzero quadratic polynomial. This cross-multiplied form remains meaningful at zeros of
      `V` or `w` (source block `jis_srcblock_e90c95146a5fe658`). -/
  classical : ∃ u0 u1 v0 v1 v2 : ℝ,
    (v0 ≠ 0 ∨ v1 ≠ 0 ∨ v2 ≠ 0) ∧
      ∀ x : ℝ, x ∈ interior domain →
        DifferentiableAt ℝ weight x ∧
          (v0 + v1 * x + v2 * x ^ 2) * deriv weight x =
            (u0 + u1 * x) * weight x

end MetaMathlibExt
