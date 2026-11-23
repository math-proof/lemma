module

public import Theorem.Random.SinglePSpace.of.All_Measurable.All_Measurable
public import Theorem.Random.SinglePSpace.of.Measurable.Measurable
public import Theorem.Random.SinglePSpace.of.Measurable
public import Def.Probability.Process.HiddenMarkovSequence.Part2
public import Class.Probability.Process.DiscreteHMM

@[expose] public section

open MeasureTheory


section

variable {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π] {x : ℕ → Ω → X} {y : ℕ → Ω → Y}

omit [Countable X] [MeasurableSingletonClass X] in
theorem IsDiscreteHMM.singlePSpace_y [h : IsDiscreteHMM π x y] (i : ℕ) : SinglePSpace π (y i) :=
  Random.SinglePSpace.of.Measurable (h.measurable_y i)

end
