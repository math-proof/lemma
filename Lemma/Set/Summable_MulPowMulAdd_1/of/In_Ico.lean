import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
`∑ k, γ ^ k * ((k + 1) * K)` is summable for `γ ∈ [0, 1)`.
-/
@[main]
private lemma main
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (K : ℝ) :
-- imply
  Summable (fun k : ℕ => γ ^ k * ((k + 1) * K)) := by
-- proof
  have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * γ ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg h₀.1]; exact h₀.2)
  have h2 := summable_geometric_of_lt_one h₀.1 h₀.2
  exact ((h1.add h2).mul_right K).congr fun k => by ring


-- created on 2026-10-06
