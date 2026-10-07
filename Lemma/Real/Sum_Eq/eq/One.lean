import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
`∑ x, 1{x₀ = x} = 1` over a finite type.
-/
@[main]
private lemma main
  [Fintype S] [DecidableEq S]
-- given
  (x₀ : S) :
-- imply
  ∑ x, (if x₀ = x then (1:ℝ) else 0) = 1 := by
-- proof
  simp


-- created on 2026-10-06
