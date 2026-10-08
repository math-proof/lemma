import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`ω ↦ 1{s[t] = x ∧ a[t] = u} * c` is integrable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A)
  (c : ℝ) :
-- imply
  Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * c) (M θ) := by
-- proof
  refine Integrable.of_bound (C := ‖c‖) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((StronglyMeasurable.discrete (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0)).comp_measurable
      ((Random.Measurable_S h₁ t).prodMk (Random.Measurable_A h₁ t))).mul stronglyMeasurable_const).aestronglyMeasurable
  ·
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> simp)


-- created on 2026-10-07
