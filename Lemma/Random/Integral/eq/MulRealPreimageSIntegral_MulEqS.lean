import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.MulRealIntegral_MulIndicator1.of.MeasurableSet
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`𝔼[f | s[t] = x] = Pr(s[t] = x)⁻¹ * 𝔼[1{s[t] = x} * f]`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (f : (ℕ → ℝ × S × A) → ℝ) :
-- imply
  ∫ ω, f ω ∂(M θ)[|s t ⁻¹' {x}] =
    ((M θ).real (s t ⁻¹' {x}))⁻¹ * ∫ ω, (if s t ω = x then (1:ℝ) else 0) * f ω ∂(M θ) := by
-- proof
  rw [Integral.eq.MulRealIntegral_MulIndicator1.of.MeasurableSet (M := M) (Random.Measurable_S h₁ t (measurableSet_singleton x)) θ]
  congr 2
  funext ω
  by_cases h : s t ω = x <;> simp [h]


-- created on 2026-10-07
