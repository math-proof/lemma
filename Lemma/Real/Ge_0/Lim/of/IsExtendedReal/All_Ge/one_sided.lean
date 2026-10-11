import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ δ a : ℝ}
-- given
  (hδ : δ > 0)
  (hlim : lim [x → x₀] f x = a)
  (hge : ∀ x ∈ Set.Ioc (x₀ - δ) x₀, f x ≥ 0) :
-- imply
  a ≥ 0 := by
-- proof
  sorry


-- created on 2026-10-11
