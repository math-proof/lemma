import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral_MulEq22.eq.MulProbIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable_Eq22
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x ∧ a[t] = u}] = Pr(s[t] = x) * π_θ(u | x)`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A) :
-- imply
  ∫ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) ∂(M θ) =
    (M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u := by
-- proof
  have := M.env.reward_markov
  have h₁ : ∀ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) =
      (if state t ω = x then (1:ℝ) else 0) * (fun z : ℝ × S × A => if z.2.2 = u then (1:ℝ) else 0) (ω t) := by
    intro ω; simp only [state, action]
    by_cases h1 : (ω t).2.1 = x <;> by_cases h2 : (ω t).2.2 = u <;> simp [h1, h2]
  simp_rw [h₁]
  rw [Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (Real.StronglyMeasurable_Eq22 u) (Norm_1.le.One) θ t x]
  have h₂ := Integral_MulEq22.eq.MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (g := fun _ => (1:ℝ)) (C := 1) stronglyMeasurable_const (by simp) θ x u
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h₂
  rw [h₂]


-- created on 2026-10-07
