import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


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
  Integrable (fun ω => φ (s t ω) (a t ω)) (M θ) := by
-- proof
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := (s_meas t).prodMk (a_meas t)
  refine Integrable.of_bound (C := ∑ p : S × A, ‖φ p.1 p.2‖)
    ((StronglyMeasurable.of_discrete (f := fun p : S × A => φ p.1 p.2)).comp_measurable
      hX).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  exact Finset.single_le_sum (f := fun p : S × A => ‖φ p.1 p.2‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (s t ω, a t ω))


-- created on 2026-10-06
