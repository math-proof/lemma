import sympy.stats.policy_trajectory.advantage
import sympy.Basic
import Lemma.Random.Measurable_R
import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma delta_meas [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] {r : ℕ → (ℕ → ℝ × S × A) → ℝ} {s : ℕ → (ℕ → ℝ × S × A) → S} {a : ℕ → (ℕ → ℝ × S × A) → A} (h₁ : ∀ t, (· t) = (r t, s t, a t)) (V : S → ℝ) (γ : ℝ) (j : ℕ) :
    Measurable (fun ω : ℕ → ℝ × S × A => r j ω + γ * V (s (j + 1) ω) - V (s j ω)) := by
  exact ((Random.Measurable_R h₁ j).add (((measurable_of_countable V).comp (Random.Measurable_S h₁ (j + 1))).const_mul γ)).sub
      ((measurable_of_countable V).comp (Random.Measurable_S h₁ j))

/--
`δ[j] • ψ(s[t], a[t])` is integrable under the trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
  {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t j : ℕ)
  (ψ : S → A → E) :
-- imply
  Integrable (fun ω => (r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω)) •
    ψ (s t ω) (a t ω)) (M θ) := by
-- proof
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := (Random.Measurable_S h₁ t).prodMk (Random.Measurable_A h₁ t)
  refine Integrable.of_bound (C := M.deltaBound γ * ∑ p : S × A, ‖ψ p.1 p.2‖)
    ((delta_meas h₁ (M.Vc θ γ) γ j).stronglyMeasurable.smul
      ((StronglyMeasurable.of_discrete (f := fun p : S × A => ψ p.1 p.2)).comp_measurable
        hX)).aestronglyMeasurable ?_
  filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico (M := M) h₀ h₁ θ] with ω h
  rw [norm_smul]
  exact mul_le_mul (h j) (Finset.single_le_sum (f := fun p : S × A => ‖ψ p.1 p.2‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))) (norm_nonneg _)
    ((norm_nonneg _).trans (h j))


-- created on 2026-10-06
