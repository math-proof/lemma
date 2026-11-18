import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`𝔼[f | s[t] = x] = ℙ(s[t] = x)⁻¹ * 𝔼[1{s[t] = x} * f]`.
Continuous-action counterpart of
`Random.Integral.eq.MulRealPreimageSIntegral_MulEqS`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (sₜ : 𝒮)
  (f : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) :
-- imply
  ∫ ω, f ω ∂(M θ)[|s t ⁻¹' {sₜ}] =
    ((M θ).real (s t ⁻¹' {sₜ}))⁻¹ *
      ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) * f ω ∂(M θ) := by
-- proof
  have hB : MeasurableSet (s t ⁻¹' {sₜ}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton sₜ)
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hB, ENNReal.toReal_inv,
    ← measureReal_def, smul_eq_mul]
  congr 1
  congr 1
  funext ω
  by_cases h : s t ω = sₜ <;> simp [h]


-- created on 2026-11-13
-- updated on 2026-11-18