import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h₀ : a ≤ b)
  (h₁ : ∀ u ∈ Set.Icc a b, 0 ≤ f u) :
-- imply
  0 ≤ ∫ u in a..b, f u :=
-- proof
  intervalIntegral.integral_nonneg h₀ h₁


-- created on 2023-03-25
-- updated on 2026-10-26
