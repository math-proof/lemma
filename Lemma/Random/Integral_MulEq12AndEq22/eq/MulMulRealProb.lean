import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral_EqSAndEqA.eq.MulRealPreimageSProb
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * φ(s[t], a[t])] = Pr(s[t] = x) * π_θ(u | x) * φ x u`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A)
  (φ : S → A → ℝ) :
-- imply
  ∫ ω, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1:ℝ) else 0) * φ (ω t).2.1 (ω t).2.2 ∂(M θ) =
    (M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u * φ x u := by
-- proof
  have h₁ : ∀ ω : ℕ → ℝ × S × A, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1:ℝ) else 0) * φ (ω t).2.1 (ω t).2.2 =
      (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * φ x u := by
    intro ω; simp only [state, action]
    by_cases h1 : (ω t).2.1 = x <;> by_cases h2 : (ω t).2.2 = u <;> simp [h1, h2]
  simp_rw [h₁]
  rw [integral_mul_const, Integral_EqSAndEqA.eq.MulRealPreimageSProb]


-- created on 2026-10-07
