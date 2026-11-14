import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real


/--
`𝔼[1{s[t] = x} * f(ω[t + j])] = ℙ(s[t] = x) * W θ f j x` for a bounded strongly measurable stage function `f`
(continuous-action trajectory model `M`, time-homogeneous `j`-step kernel expectation `W`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : StronglyMeasurable f)
  (h₂ : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (t j : ℕ)
  (x : 𝒮) :
-- imply
  ∫ ω, (if s t ω = x then (1:ℝ) else 0) * f (ω (t + j)) ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * ∫ z, M.Kf θ f j z ∂(M.stageK θ x) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  have hK := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) h₁ h₂ θ j
  exact (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) h₁ h₂ (Real.StronglyMeasurable_Eq12 x) Norm_1.le.One θ t j).trans
    (Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      h₀ (M := M) hK.1 hK.2 θ t x)


-- created on 2026-11-13
