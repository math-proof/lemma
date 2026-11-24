module
public import Theorem.Random.SinglePSpace.of.Measurable.Measurable
public import Theorem.Random.SinglePSpace.of.Measurable
public import Def.Probability.Process.HiddenMarkovSequence.Part2
public import Theorem.Probability.Process.DiscreteHMM
open MeasureTheory


public section

section

variable {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π] {x : ℕ → Ω → X} {y : ℕ → Ω → Y}

instance [h : IsDiscreteHMM π x y] (i j : ℕ) : SinglePSpace π (x i, y j) :=
  Random.SinglePSpace.of.Measurable.Measurable
    (h.measurable_x i) (h.measurable_y j)

end
