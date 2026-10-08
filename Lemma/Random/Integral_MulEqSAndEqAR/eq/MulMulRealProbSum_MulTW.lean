import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.MEqR_Rc
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEq12AndEq22.eq.MulMulRealProb
import Lemma.Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable_Eq12AndEq22
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * r[t+j+1]] = Pr(s[t] = x) * π_θ(u | x) * ∑ y, T(x, u, y) * W θ rc j y`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t j : ℕ)
  (x : S)
  (u : A) :
-- imply
  ∫ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * reward (t + (j + 1)) ω ∂(M θ) =
    (M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u * ∑ y, M.T x u y * M.W θ M.rc j y := by
-- proof
  have h₀ : ∫ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * reward (t + (j + 1)) ω ∂(M θ) =
      ∫ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * M.rc (ω (t + (j + 1))) ∂(M θ) :=
    integral_congr_ae ((MEqR_Rc (M := M) θ (t + (j + 1))).mono fun ω h => by dsimp only; rw [h])
  rw [h₀]
  refine (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) (Real.StronglyMeasurable_Eq12AndEq22 x u) (Norm_1.le.One) θ t (j + 1)).trans ?_
  simp_rw [Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ j]
  exact Integral_MulEq12AndEq22.eq.MulMulRealProb (M := M) θ t x u (fun x' u' => ∑ y, M.T x' u' y * M.W θ M.rc j y)


-- created on 2026-10-07
