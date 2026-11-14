import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
`𝔼[f | s[t] = x] = ℙ(s[t] = x)⁻¹ * 𝔼[1{s[t] = x} * f]`.
Continuous-action counterpart of
`Random.Integral.eq.MulRealPreimageSIntegral_MulEqS`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : 𝒮)
  (f : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) :
-- imply
  ∫ ω, f ω ∂(M θ)[|s t ⁻¹' {x}] =
    ((M θ).real (s t ⁻¹' {x}))⁻¹ *
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * f ω ∂(M θ) := by
-- proof
  have hB : MeasurableSet (s t ⁻¹' {x}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hB, ENNReal.toReal_inv,
    ← measureReal_def, smul_eq_mul]
  congr 1
  congr 1
  funext ω
  by_cases h : s t ω = x <;> simp [h]


-- created on 2026-11-13
