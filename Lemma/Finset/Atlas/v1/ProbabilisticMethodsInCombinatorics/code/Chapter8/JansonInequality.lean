import Mathlib
import Initialize.Tactic.Attr.Basic
open Real Finset BigOperators MeasureTheory


namespace JansonInequality

/--
[janson_inequality_II](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/JansonInequality.lean)
-/
@[path]
lemma janson_inequality_II
  {μ Δ v : ℝ}
-- given
  (hμ_pos : 0 < μ)
  (hΔ_ge_μ : Δ ≥ μ)
  (hbound : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → v ≤ Real.exp (-q * μ + q ^ 2 * Δ / 2)) :
-- imply
  v ≤ Real.exp (-(μ ^ 2) / (2 * Δ)) := by
-- proof
  have hΔ_pos : (0 : ℝ) < Δ := lt_of_lt_of_le hμ_pos hΔ_ge_μ
  have hq_nonneg : (0 : ℝ) ≤ μ / Δ := div_nonneg (le_of_lt hμ_pos) (le_of_lt hΔ_pos)
  have hq_le_one : μ / Δ ≤ 1 := div_le_one_of_le₀ hΔ_ge_μ (le_of_lt hΔ_pos)
  have key := hbound (μ / Δ) hq_nonneg hq_le_one
  suffices h : -(μ / Δ) * μ + (μ / Δ) ^ 2 * Δ / 2 = -(μ ^ 2) / (2 * Δ) by
    rwa [h] at key
  field_simp
  ring

end JansonInequality


-- created on 2026-10-23
