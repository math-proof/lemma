import sympy.stats.policy_trajectory.gradient
import Lemma.Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Integrable_G.of.In_Ico
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`G[t] • ψ(s[t], a[t])` is integrable under the trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (ψ : S → A → E) :
-- imply
  Integrable (fun ω => ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω • ψ (s t ω) (a t ω)) (M θ) := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := (Random.Measurable_S h₁ t).prodMk (Random.Measurable_A h₁ t)
  refine Integrable.of_bound (C := (1 - γ)⁻¹ * |M.env.R| * ∑ p : S × A, ‖ψ p.1 p.2‖)
    ((Integrable_G.of.In_Ico (M := M) h₀ h₁ θ t).1.smul ((StronglyMeasurable.of_discrete
      (f := fun p : S × A => ψ p.1 p.2)).comp_measurable hX).aestronglyMeasurable) ?_
  filter_upwards [AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ t] with ω h
  rw [norm_smul]
  exact mul_le_mul h.2 (Finset.single_le_sum (f := fun p : S × A => ‖ψ p.1 p.2‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))) (norm_nonneg _)
    ((norm_nonneg _).trans h.2)


-- created on 2026-10-06
