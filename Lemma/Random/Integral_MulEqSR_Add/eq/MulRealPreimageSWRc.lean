import Lemma.Random.MEq_Clip.of.All_Eq
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormClip.le.AbsR
import Lemma.Random.StronglyMeasurableClip
import Lemma.Real.Norm_1.le.One
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x} * r[t+j]] = ℙ(s[t] = x) * W θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) j x`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t j : ℕ)
  (x : S) :
-- imply
  ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + j) ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) j z ∂(M.stageK θ x) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  have h₂ : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + j) ω ∂(M θ) =
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * clip (ω (t + j)).1 (-M.env.R) M.env.R ∂(M θ) :=
    integral_congr_ae ((MEq_Clip.of.All_Eq h₀ (M := M) θ (t + j)).mono fun ω h => by dsimp only; rw [h])
  have hK := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) θ j
  rw [h₂]
  exact (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) (Real.StronglyMeasurable_Eq12 x) (Norm_1.le.One) θ t j).trans
    (Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable h₀ (M := M) hK.1 hK.2 θ t x)


-- created on 2026-10-07
-- updated on 2026-10-12
