import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Lemma.Random.SinglePSpace.of.Measurable.Measurable
import Lemma.Random.SinglePSpace.of.Measurable
import Def.Probability.Process.HiddenMarkovSequence.Part2
import Instance.Probability.Process.DiscreteHMM
open MeasureTheory


section

variable {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π] {x : ℕ → Ω → X} {y : ℕ → Ω → Y}

omit [Countable X] [MeasurableSingletonClass X] in
theorem IsDiscreteHMM.singlePSpace_yy [h : IsDiscreteHMM π x y] (i j : ℕ) : SinglePSpace π (y i, y j) :=
  Random.SinglePSpace.of.Measurable.Measurable
    (h.measurable_y i) (h.measurable_y j)

omit [Countable Y] [MeasurableSingletonClass Y] in
theorem IsDiscreteHMM.singlePSpace_x [h : IsDiscreteHMM π x y] (a b : ℤ) : SinglePSpace π x[a:b] :=
  Random.SinglePSpace.of.Measurable
    (Measurable.of_eval fun _ => h.measurable_x _)

end
