import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral_EqSAndEqA.eq.MulRealPreimageSProb
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`Pr(s[t] = x ∧ a[t] = u) = Pr(s[t] = x) * π_θ(u | x)`.
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
  (M θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) = (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u := by
-- proof
  rw [← Integral_EqSAndEqA.eq.MulRealPreimageSProb (M := M) θ t x u, ← integral_indicator_one
    ((Random.Measurable_S t (measurableSet_singleton x)).inter (Random.Measurable_A t (measurableSet_singleton u)))]
  congr 1
  funext ω
  by_cases h1 : s t ω = x <;> by_cases h2 : a t ω = u <;> simp [h1, h2]


-- created on 2026-10-07
