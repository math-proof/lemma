import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
Every function of `(s[t], a[t])` (finite state / action spaces) is integrable under the trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  [NormedAddCommGroup E]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (φ : 𝒮 → 𝒜 → E) :
-- imply
  Integrable (fun ω => φ (s t ω) (a t ω)) (M θ) := by
-- proof
  have hX : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s t ω, a t ω)) :=
    (Random.Measurable.of.All_Eq.snd.fst h₀ t).prodMk
      (Random.Measurable.of.All_Eq.snd.snd h₀ t)
  refine Integrable.of_bound (C := ∑ p : 𝒮 × 𝒜, ‖φ p.1 p.2‖)
    ((StronglyMeasurable.of_discrete (f := fun p : 𝒮 × 𝒜 => φ p.1 p.2)).comp_measurable
      hX).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  exact Finset.single_le_sum (f := fun p : 𝒮 × 𝒜 => ‖φ p.1 p.2‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (s t ω, a t ω))


-- created on 2026-10-06
-- updated on 2026-11-14
