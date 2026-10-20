import Mathlib.Topology.MetricSpace.Pseudo.Defs
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ a : ℝ}
-- given
  (h₀ : Filter.Tendsto f (nhdsWithin x₀ {x₀}ᶜ) (nhds a)) :
-- imply
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - x₀| → |x - x₀| < δ → |f x - a| < ε := by
-- proof
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.tendsto_nhdsWithin_nhds.mp h₀ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx0 hxδ
  have hx : x ≠ x₀ := sub_ne_zero.mp (abs_pos.mp hx0)
  simpa [Real.dist_eq] using h hx (by simpa [Real.dist_eq] using hxδ)


-- created on 2020-06-23
-- updated on 2026-10-17
