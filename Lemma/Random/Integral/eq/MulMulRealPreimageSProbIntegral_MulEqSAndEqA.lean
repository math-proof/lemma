import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.MulRealIntegral_MulIndicator1.of.MeasurableSet
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
import Lemma.Random.RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`𝔼[f | s[t] = x, a[t] = u] = (Pr(s[t] = x) * π_θ(u | x))⁻¹ * 𝔼[1{s[t] = x ∧ a[t] = u} * f]`.
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
  (f : (ℕ → ℝ × S × A) → ℝ) :
-- imply
  ∫ ω, f ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
    ((M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u)⁻¹ *
      ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * f ω ∂(M θ) := by
-- proof
  rw [Integral.eq.MulRealIntegral_MulIndicator1.of.MeasurableSet (M := M) ((Random.Measurable_S h₁ t (measurableSet_singleton x)).inter (Random.Measurable_A h₁ t (measurableSet_singleton u))) θ,
    RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb h₁]
  congr 2
  funext ω
  by_cases h1 : s t ω = x <;> by_cases h2 : a t ω = u <;> simp [h1, h2]


-- created on 2026-10-07
