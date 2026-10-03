import Lemma.Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory


/--
The joint law of two prefix vectors `x[:n]` and `y[:m]` of discrete random sequences has a density.
If every `x k : Ω → α` and `y k : Ω → β` is measurable and `α`, `β` are countable (with measurable
singletons), then `(x[:n], y[:m])` spans a `SinglePSpace π`; the reference measure on the vector
types `Fin _ → α` is the counting measure by instance.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → α} {y : ℕ → Ω → β}
  {n m : ℤ}
-- given
  (hx : ∀ k, Measurable (x k))
  (hy : ∀ k, Measurable (y k)) :
-- imply
  SinglePSpace π (x[:n], y[:m]) := by
-- proof
  apply Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
    (measurable_pi_lambda _ fun _ => hx _) (measurable_pi_lambda _ fun _ => hy _) rfl rfl


-- created on 2026-10-03
