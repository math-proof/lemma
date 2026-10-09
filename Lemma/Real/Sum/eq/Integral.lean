import sympy.integrals.integrals
import sympy.Basic


@[path]
private lemma main
  {f : ℕ → ℝ → ℝ}
  {n : ℕ}
  {a b : ℝ}
-- given
  (h : ∀ x ∈ Finset.range n, IntervalIntegrable (f x) MeasureTheory.volume a b) :
-- imply
  ∑ x ∈ Finset.range n, ∫ y : ℝ in a..b, f x y
    = ∫ y : ℝ in a..b, ∑ x ∈ Finset.range n, f x y := by
-- proof
  exact (intervalIntegral.integral_finsetSum h).symm


-- created on 2023-03-27
-- updated on 2023-04-04
