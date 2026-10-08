import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The action process `a t` of the trajectory space is measurable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A]
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (t : ℕ) :
-- imply
  Measurable (a t) := by
-- proof
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  exact measurable_snd.snd.comp (measurable_pi_apply t)


-- created on 2026-10-07
