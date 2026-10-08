import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x} * f(ω[t + j])] = Pr(s[t] = x) * W θ f j x` for a bounded strongly measurable stage function `f`
(trajectory model `M`, time-homogeneous `j`-step kernel expectation `W`).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {f : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (θ : Θ)
  (h₀ : StronglyMeasurable f)
  (h₁ : ∀ z, ‖f z‖ ≤ C)
  (t j : ℕ)
  (x : S) :
-- imply
  ∫ ω, (if state t ω = x then (1:ℝ) else 0) * f (ω (t + j)) ∂(M θ) =
    (M θ).real (state t ⁻¹' {x}) * M.W θ f j x := by
-- proof
  have hK := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) h₀ h₁ θ j
  exact (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) h₀ h₁ (Real.StronglyMeasurable_Eq12 x) (Norm_1.le.One) θ t j).trans (Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable (M := M) hK.1 hK.2 θ t x)


-- created on 2026-10-06
