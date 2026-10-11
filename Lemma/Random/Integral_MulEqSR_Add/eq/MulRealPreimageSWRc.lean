import sympy.stats.policy_trajectory
import sympy.functions.elementary.miscellaneous
import sympy.Basic
import Lemma.Random.MEqR_Rc
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormRc.le.AbsR
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.W.eq.Integral
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x} * r[t+j]] = Pr(s[t] = x) * W θ rc j x`.
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
  let rc (z : ℝ × S × A) : ℝ := clip z.1 (-M.env.R) M.env.R
  ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + j) ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * M.W θ rc j x := by
-- proof
  intro rc
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  have h₂ : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + j) ω ∂(M θ) =
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * rc (ω (t + j)) ∂(M θ) :=
    integral_congr_ae ((MEqR_Rc h₀ (M := M) θ (t + j)).mono fun ω h => by dsimp only; rw [h])
  have hK := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.AbsR (M := M)) θ j
  rw [h₂]
  refine (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.AbsR (M := M)) (Real.StronglyMeasurable_Eq12 x) (Norm_1.le.One) θ t j).trans ?_
  refine (Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable h₀ (M := M) hK.1 hK.2 θ t x).trans ?_
  rw [W.eq.Integral (M := M) θ j x]


-- created on 2026-10-07
-- updated on 2026-10-11
