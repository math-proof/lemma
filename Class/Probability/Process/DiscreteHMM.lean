import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Lemma.Random.SinglePSpace.of.Measurable.Measurable
import Lemma.Random.SinglePSpace.of.Measurable
import Def.Probability.Process.HiddenMarkovSequence.Part2
open MeasureTheory


/-- `x` (observations) and `y` (hidden labels) form a first-order hidden Markov model over discrete
(counting-measure) spaces: every `x k`, `y k` is measurable, `X` and `Y` carry the counting measure
(`[CountableMeasure X]` / `[CountableMeasure Y]`),
`x (t + 1)` is independent of the past `(x[:t + 1], y[:t + 1])` given `y (t + 1)` (emission), and
`y (t + 1)` is independent of `(x[:t + 1], y[:t])` given `y t` (first-order Markov property). -/
class IsDiscreteHMM {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [CountableMeasure Y] [CountableMeasure X]
    (π : Measure Ω) [IsProbabilityMeasure π] (x : ℕ → Ω → X) (y : ℕ → Ω → Y) : Prop where
  measurable_x : ∀ k, Measurable (x k)
  measurable_y : ∀ k, Measurable (y k)
  emit : ∀ t, ∀ _ : Measurable (y (t + 1)),
    x (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t + 1]) | y (t + 1)
  markov : ∀ t, ∀ _ : Measurable (y t),
    y (t + 1) ⟂ᵢ[π] (x[:t + 1], y[:t]) | y t

