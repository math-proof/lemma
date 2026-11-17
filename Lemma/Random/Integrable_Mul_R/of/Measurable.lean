import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`ω ↦ φ(X ω) * r[t]` is integrable for a measurable finite-valued `X`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {X : (ℕ → ℝ × 𝒮 × 𝒜) → B}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hX : Measurable X)
  (θ : Θ)
  (φ : B → ℝ)
  (t : ℕ) :
-- imply
  Integrable (fun ω => φ (X ω) * r t ω) (M.traj θ) := by
-- proof
  refine Integrable.of_bound (C := (∑ b, ‖φ b‖) * |M.R|) ?_ ((MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) θ t).mono fun ω h => ?_)
  · exact (((StronglyMeasurable.of_discrete (f := φ)).comp_measurable hX).mul
      (Random.Measurable.of.All_Eq.fst h₀ t).stronglyMeasurable).aestronglyMeasurable
  ·
    rw [norm_mul, h]
    exact mul_le_mul (Finset.single_le_sum (f := fun b => ‖φ b‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ _)) (NormClip.le.Abs_R M.R _) (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))


-- created on 2026-10-07
-- updated on 2026-11-17