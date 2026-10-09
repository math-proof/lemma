import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma by_parts
  {u v : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hu : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ u x)
  (hv : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ v x)
  (hu' : IntervalIntegrable (deriv u) MeasureTheory.volume a b)
  (hv' : IntervalIntegrable (deriv v) MeasureTheory.volume a b) :
-- imply
  ∫ x in a..b, u x * deriv v x = u b * v b - u a * v a - ∫ x in a..b, deriv u x * v x := by
-- proof
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x hx => (hu x hx).hasDerivAt) (fun x hx => (hv x hx).hasDerivAt) hu' hv'


@[path]
private lemma split
  {f : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hab : IntervalIntegrable f MeasureTheory.volume a b)
  (hbc : IntervalIntegrable f MeasureTheory.volume b c) :
-- imply
  ∫ x in a..c, f x = (∫ x in a..b, f x) + ∫ x in b..c, f x := by
-- proof
  exact (intervalIntegral.integral_add_adjacent_intervals hab hbc).symm


-- created on 2020-06-07
