import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.EqW
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm.le.Sum_Norm
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable.discrete
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x} * f(s[t+1])] = Pr(s[t] = x) * ∑ u, π_θ(u | x) * ∑ y, T(x, u, y) * f y`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (f : S → ℝ) :
-- imply
  ∫ ω, (if s t ω = x then (1:ℝ) else 0) * f (s (t + 1) ω) ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * ∑ u, M.pol.prob θ x u * ∑ y, M.T x u y * f y := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  have hf : StronglyMeasurable (fun z : ℝ × S × A => f z.2.1) := (StronglyMeasurable.discrete f).comp_measurable measurable_snd.fst
  have hK := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf (fun z => Norm.le.Sum_Norm f z.2.1) θ 1
  refine (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) hf (fun z => Norm.le.Sum_Norm f z.2.1) (Real.StronglyMeasurable_Eq12 x) (Norm_1.le.One) θ t 1).trans ?_
  refine (Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable h₁ (M := M) hK.1 hK.2 θ t x).trans ?_
  congr 1
  show M.W θ (fun z => f z.2.1) (0 + 1) x = _
  rw [WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf (fun z => Norm.le.Sum_Norm f z.2.1) θ 0]
  simp_rw [Random.EqW]


-- created on 2026-10-07
