import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.MEqR_Rc
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x} * r[t+j]] = Pr(s[t] = x) * W θ rc j x`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t j : ℕ)
  (x : S) :
-- imply
  ∫ ω, (if state t ω = x then (1:ℝ) else 0) * reward (t + j) ω ∂(M θ) =
    (M θ).real (state t ⁻¹' {x}) * M.W θ M.rc j x := by
-- proof
  have h₁ : ∫ ω, (if state t ω = x then (1:ℝ) else 0) * reward (t + j) ω ∂(M θ) =
      ∫ ω, (if state t ω = x then (1:ℝ) else 0) * M.rc (ω (t + j)) ∂(M θ) :=
    integral_congr_ae ((MEqR_Rc (M := M) θ (t + j)).mono fun ω h => by dsimp only; rw [h])
  have hK := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ j
  rw [h₁]
  exact (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) (Real.StronglyMeasurable_Eq12 x) (Norm_1.le.One) θ t j).trans
    (Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable (M := M) hK.1 hK.2 θ t x)


-- created on 2026-10-07
