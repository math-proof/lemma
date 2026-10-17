import Mathlib.Topology.MetricSpace.Pseudo.Defs
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ A : ℝ}
-- given
  (h₀ : A < 0)
  (h₁ : Filter.Tendsto f (nhdsWithin x₀ {x₀}ᶜ) (nhds A)) :
-- imply
  ∃ δ > 0, ∀ x, 0 < |x - x₀| → |x - x₀| < δ → f x < A / 2 := by
-- proof
  obtain ⟨δ, hδ, h⟩ := Metric.tendsto_nhdsWithin_nhds.mp h₁ (-A / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x hx0 hxδ
  have hx : x ≠ x₀ := sub_ne_zero.mp (abs_pos.mp hx0)
  have hlt : |f x - A| < -A / 2 := by
    simpa [Real.dist_eq] using h hx (by simpa [Real.dist_eq] using hxδ)
  have hle : f x - A ≤ |f x - A| := le_abs_self _
  linarith


-- created on 2026-10-11
-- updated on 2026-10-17
