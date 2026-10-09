import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- The probability-notation assumptions give the abstract factorization for the family of prefix joint probabilities
`P t ys = Pr(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])`. -/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure Y]
  [ReferenceMeasure X]
  [Countable Y]
  [MeasurableSingletonClass Y]
  [Countable X]
  [MeasurableSingletonClass X]
  {π : Measure Ω} {x : ℕ → Ω → X} {y : ℕ → Ω → Y} [∀ i, SinglePSpace π (y i)] [∀ i j, SinglePSpace π (x i, y j)] [∀ i j, SinglePSpace π (y i, y j)] [∀ n, SinglePSpace π (x[:n], y[:n])]
  {xo : ℕ → X}
  {P : ℕ → (ℕ → Y) → ℝ}
-- given
  (h : IsHiddenMarkovPr π x y xo)
  (hP : ∀ t ys, P t ys = (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ)) :
-- imply
  IsHiddenMarkovFac π x y xo P := by
-- proof
  exact fun ys =>
    ⟨by rw [hP]; exact (h ys).1, fun t => by rw [hP, hP]; exact (h ys).2 t⟩


-- created on 2026-10-07
