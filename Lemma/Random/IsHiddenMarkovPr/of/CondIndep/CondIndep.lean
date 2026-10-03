import Lemma.Random.Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
import sympy.stats.hidden_markov_sequence
import sympy.stats.ennreal_coe
import sympy.Basic
open MeasureTheory
open scoped ENNReal.ToRealCoe


/--
The emission independence `x (t + 1) ⟂ (x[:t + 1], y[:t + 1]) | y (t + 1)` and the first-order Markov
property `y (t + 1) ⟂ (x[:t + 1], y[:t]) | y t` give the one-step factorization of the prefix probabilities
(`IsHiddenMarkovPr`) used by the CRF lemmas.
-/
@[main]
private lemma main
  {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {xo : ℕ → X}
  [∀ i, SinglePSpace π (y i)]
  [∀ i j, SinglePSpace π (x i, y j)]
  [∀ i j, SinglePSpace π (y i, y j)]
  [∀ n, SinglePSpace π (x[:n], y[:n])]
-- given
  (hx : ∀ k, Measurable (x k))
  (hy : ∀ k, Measurable (y k))
  (hX : ReferenceMeasure.measure (α := X) = Measure.count)
  (hY : ReferenceMeasure.measure (α := Y) = Measure.count)
  (h_emit : ∀ t, ∀ _ : Measurable (y (t + 1)),
    x (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t + 1]) | y (t + 1))
  (h_markov : ∀ t, ∀ _ : Measurable (y t),
    y (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t]) | y t) :
-- imply
  IsHiddenMarkovPr π x y xo := by
-- proof
  intro ys
  obtain ⟨h₀, h₁⟩ := Random.Prob.eq.Mul_ProbS.Prob.eq.Mul_MulProbS.of.CondIndep.CondIndep
    (xo := xo) hx hy hX hY h_emit h_markov ys
  refine ⟨?_, fun t => ?_⟩
  · rw [h₀, ENNReal.toReal_mul]
  · rw [h₁ t, ENNReal.toReal_mul, ENNReal.toReal_mul]


-- created on 2026-10-02