import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Every function of `(s[t], a[t])` (finite state / action spaces) is integrable under the trajectory model.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {E : Type*}
  [NormedAddCommGroup E]
-- given
  (θ : Θ)
  (t : ℕ)
  (φ : S → A → E) :
-- imply
  Integrable (fun ω => φ (state t ω) (action t ω)) (M θ) := by
-- proof
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (state t ω, action t ω)) := (Random.Measurable_S t).prodMk (Random.Measurable_A t)
  refine Integrable.of_bound (C := ∑ p : S × A, ‖φ p.1 p.2‖)
    ((StronglyMeasurable.of_discrete (f := fun p : S × A => φ p.1 p.2)).comp_measurable
      hX).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  exact Finset.single_le_sum (f := fun p : S × A => ‖φ p.1 p.2‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (state t ω, action t ω))


-- created on 2026-10-06
