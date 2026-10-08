import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.EqW
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEq12AndEq22.eq.MulMulRealProb
import Lemma.Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm.le.Sum_Norm
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable.discrete
import Lemma.Real.StronglyMeasurable_Eq12AndEq22
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * f(s[t+1])] = Pr(s[t] = x) * π_θ(u | x) * ∑ y, T(x, u, y) * f y`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A)
  (f : S → ℝ) :
-- imply
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * f (s (t + 1) ω) ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * ∑ y, M.T x u y * f y := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have hf : StronglyMeasurable (fun z : ℝ × S × A => f z.2.1) := (StronglyMeasurable.discrete f).comp_measurable measurable_snd.fst
  refine (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) hf (fun z => Norm.le.Sum_Norm f z.2.1) (Real.StronglyMeasurable_Eq12AndEq22 x u) (Norm_1.le.One) θ t 1).trans ?_
  simp_rw [Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf (fun z => Norm.le.Sum_Norm f z.2.1) θ 0, Random.EqW]
  exact Integral_MulEq12AndEq22.eq.MulMulRealProb (M := M) h₁ θ t x u (fun x' u' => ∑ y, M.T x' u' y * f y)


-- created on 2026-10-07
