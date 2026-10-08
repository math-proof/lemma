import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Integrable_G.of.In_Ico
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`G[t] • ψ(s[t], a[t])` is integrable under the trajectory model.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
  {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (ψ : S → A → E) :
-- imply
  Integrable (fun ω => G γ t ω • ψ (state t ω) (action t ω)) (M θ) := by
-- proof
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (state t ω, action t ω)) := (Random.Measurable_S t).prodMk (Random.Measurable_A t)
  refine Integrable.of_bound (C := (1 - γ)⁻¹ * |M.env.R| * ∑ p : S × A, ‖ψ p.1 p.2‖)
    ((Integrable_G.of.In_Ico (M := M) θ h₀ t).1.smul ((StronglyMeasurable.of_discrete
      (f := fun p : S × A => ψ p.1 p.2)).comp_measurable hX).aestronglyMeasurable) ?_
  filter_upwards [AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) θ h₀ t] with ω h
  rw [norm_smul]
  exact mul_le_mul h.2 (Finset.single_le_sum (f := fun p : S × A => ‖ψ p.1 p.2‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ (state t ω, action t ω))) (norm_nonneg _)
    ((norm_nonneg _).trans h.2)


-- created on 2026-10-06
