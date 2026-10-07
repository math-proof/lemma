import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Pull a finite weighted sum out of a discounted series:
`∑' k, γ ^ k * ∑ i, c i * w i k = ∑ i, c i * ∑' k, γ ^ k * w i k`.
-/
@[main]
private lemma main
  [Fintype ι]
  {γ : ℝ}
-- given
  (w : ι → ℕ → ℝ)
  (hw : ∀ i, Summable (fun k => γ ^ k * w i k))
  (c : ι → ℝ) :
-- imply
  ∑' k, γ ^ k * ∑ i, c i * w i k = ∑ i, c i * ∑' k, γ ^ k * w i k := by
-- proof
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun i _ => ((hw i).mul_left (c i)).congr (fun k => by ring))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← tsum_mul_left]
  congr 1; funext k; ring


-- created on 2026-10-07
