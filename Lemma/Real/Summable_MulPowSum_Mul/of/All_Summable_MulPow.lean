import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
A finite weighted sum of summable discounted series is summable: `Summable (fun k => γ ^ k * ∑ i, c i * w i k)`.
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
  Summable (fun k => γ ^ k * ∑ i, c i * w i k) := by
-- proof
  simp_rw [Finset.mul_sum]
  exact summable_sum (fun i _ => ((hw i).mul_left (c i)).congr (fun k => by ring))


-- created on 2026-10-07
