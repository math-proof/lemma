import Mathlib.Topology.MetricSpace.Pseudo.Defs
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ A : ℝ}
-- given
  (h₀ : A ≠ 0)
  (h₁ : Filter.Tendsto f (nhdsWithin x₀ {x₀}ᶜ) (nhds A)) :
-- imply
  ∃ δ > 0, ∀ x, 0 < |x - x₀| → |x - x₀| < δ → |A| / 2 < |f x| := by
-- proof
  obtain ⟨δ, hδ, h⟩ := Metric.tendsto_nhdsWithin_nhds.mp h₁ (|A| / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x hx0 hxδ
  have hx : x ≠ x₀ := sub_ne_zero.mp (abs_pos.mp hx0)
  have hlt : |f x - A| < |A| / 2 := by
    simpa [Real.dist_eq] using h hx (by simpa [Real.dist_eq] using hxδ)
  have habs : |A| - |f x| ≤ |f x - A| := by
    simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub A (f x)
  linarith


-- created on 2020-05-15
-- updated on 2026-10-17
