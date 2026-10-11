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
@[path]
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
  (u : A) :
-- imply
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u := by
-- proof
  have := M.env.reward_markov
  have h₃ : ∀ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) =
      (if s t ω = x then (1:ℝ) else 0) * (fun z : ℝ × S × A => if z.2.2 = u then (1:ℝ) else 0) (ω t) := by
    intro ω
    have hs : s t ω = (ω t).2.1 := (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
    have ha : a t ω = (ω t).2.2 := (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
    simp only [hs, ha]
    by_cases h1 : (ω t).2.1 = x <;> by_cases h2 : (ω t).2.2 = u <;> simp [h1, h2]
  simp_rw [h₃]
  rw [Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable h₁ (M := M) (Real.StronglyMeasurable_Eq22 u) (Norm_1.le.One) θ t x]
  have h₂ := Integral_MulEq22.eq.MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (g := fun _ => (1:ℝ)) (C := 1) stronglyMeasurable_const (by simp) θ x u
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h₂
  rw [h₂]


-- created on 2026-10-07
