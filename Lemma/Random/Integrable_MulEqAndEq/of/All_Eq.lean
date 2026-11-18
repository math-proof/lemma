import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`ω ↦ 1{s[t] = x ∧ a[t] = u} * c` is integrable.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (sₜ : 𝒮)
  (aₜ : 𝒜)
  (c : ℝ) :
-- imply
  Integrable (fun ω => (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) * c) (M θ) := by
-- proof
  refine Integrable.of_bound (C := ‖c‖) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((StronglyMeasurable.of_discrete (f := (fun p : 𝒮 × 𝒜 => if p.1 = sₜ ∧ p.2 = aₜ then (1:ℝ) else 0))).comp_measurable
      ((Random.Measurable.of.All_Eq.snd.fst h₀ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₀ t))).mul stronglyMeasurable_const).aestronglyMeasurable
  ·
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> simp)


-- created on 2026-10-07
-- updated on 2026-11-18