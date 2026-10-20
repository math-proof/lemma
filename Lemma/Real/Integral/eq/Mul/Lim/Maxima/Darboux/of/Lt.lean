import Lemma.Real.Integral.eq.Mul.Lim.Riemann.of.Lt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open intervalIntegral Finset Filter Set Real


/--
Riemann-sum form of the integral on a compact interval, with the bounds ordered increasingly.
-/
@[path]
private lemma main
  {f : ℝ → ℝ} {a b : ℝ}
  (h₀ : a < b)
  (h₁ : ContinuousOn f (Icc a b)) :
-- imply
  (∫ x in a..b, f x) =
    (b - a) * limUnder atTop (fun n : ℕ =>
      (∑ k ∈ range n, f (a + (b - a) * (k : ℝ) / n)) / n) := by
-- proof
  apply Integral.eq.Mul.Lim.Riemann.of.Lt h₀ h₁


-- created on 2020-05-26
-- updated on 2026-10-17
