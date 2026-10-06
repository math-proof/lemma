import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.Basic


open MeasureTheory


@[main]
private lemma main
  {u v : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hu : ContinuousOn u (Set.uIcc a b))
  (hv : ContinuousOn v (Set.uIcc a b))
  (hu' : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt u (deriv u x) x)
  (hv' : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt v (deriv v x) x)
  (hu'int : IntervalIntegrable (deriv u) volume a b)
  (hv'int : IntervalIntegrable (deriv v) volume a b) :
-- imply
  ∫ x in a..b, u x * deriv v x = u b * v b - u a * v a - ∫ x in a..b, deriv u x * v x :=
-- proof
  intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv hu' hv' hu'int hv'int


-- created on 2020-06-07
-- updated on 2023-07-03
