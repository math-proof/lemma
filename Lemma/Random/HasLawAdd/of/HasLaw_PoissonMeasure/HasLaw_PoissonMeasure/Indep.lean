import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory
open scoped NNReal


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x y : Ω → ℕ}
  {r₀ r₁ : NNReal}
-- given
  (h₀ : x ⟂ᵢ[π] y)
  (h₁ : HasLaw x (poissonMeasure r₀) π)
  (h₂ : HasLaw y (poissonMeasure r₁) π) :
-- imply
  HasLaw (x + y) (poissonMeasure (r₀ + r₁)) π :=
-- proof
  h₀.hasLaw_add_poissonMeasure h₁ h₂


-- created on 2021-07-18
-- updated on 2026-10-26
