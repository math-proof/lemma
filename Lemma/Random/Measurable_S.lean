import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The state process `s t` of the trajectory space is measurable.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A]
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (t : ℕ) :
-- imply
  Measurable (s t) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  exact measurable_snd.fst.comp (measurable_pi_apply t)


-- created on 2026-10-07
