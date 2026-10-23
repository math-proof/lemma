import Lemma.Random.EqW
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm_1.le.One
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


private lemma w0 [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] (M : Model Θ S A) (θ : Θ) (f : S → ℝ) (y' : S) :
  ∫ z, M.Kf θ (fun z => f z.2.1) 0 z ∂(M.stageK θ y') = f y' := by
  rw [show M.Kf θ (fun z => f z.2.1) 0 = fun z => f z.2.1 from funext fun z => rfl]
  exact Random.EqW (M := M) θ f y'


/--
`𝔼[1{s[t] = x} * f(s[t+1])] = ℙ(s[t] = x) * ∑ u, π_θ(u | x) * ∑ y, T(x, u, y) * f y`.
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
  (t : ℕ)
  (x : S)
  (f : S → ℝ) :
-- imply
  ∫ ω, (if s t ω = x then (1:ℝ) else 0) * f (s (t + 1) ω) ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * ∑ u, M.policy.prob θ x u * ∑ y, (M.env.trans (x, u)).real {y} * f y := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  have hf : StronglyMeasurable (fun z : ℝ × S × A => f z.2.1) := (StronglyMeasurable.of_discrete (f := f)).comp_measurable measurable_snd.fst
  have hK := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf (fun z => Norm.le.Sum_Norm f z.2.1) θ 1
  refine (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) hf (fun z => Norm.le.Sum_Norm f z.2.1) (Real.StronglyMeasurable_Eq12 x) (Norm_1.le.One) θ t 1).trans ?_
  refine (Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable h₀ (M := M) hK.1 hK.2 θ t x).trans ?_
  congr 1
  show ∫ z, M.Kf θ (fun z => f z.2.1) (0 + 1) z ∂(M.stageK θ x) = _
  rw [WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf (fun z => Norm.le.Sum_Norm f z.2.1) θ 0]
  refine Finset.sum_congr rfl fun u _ => congrArg (fun inner => M.policy.prob θ x u * inner) ?_
  refine Finset.sum_congr rfl fun y _ => by rw [w0 (M := M) θ f y]


-- created on 2026-10-07
