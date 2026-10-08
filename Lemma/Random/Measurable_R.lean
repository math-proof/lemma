import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient


/--
The reward coordinate `r[k]` of the trajectory is measurable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A]
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (k : ℕ) :
-- imply
  Measurable (r k) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  exact measurable_fst.comp (measurable_pi_apply k)


-- created on 2026-10-06
