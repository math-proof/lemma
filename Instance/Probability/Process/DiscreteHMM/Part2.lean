import Lemma.Random.SinglePSpace.of.All_Measurable.All_Measurable
import Lemma.Random.SinglePSpace.of.Measurable.Measurable
import Lemma.Random.SinglePSpace.of.Measurable
import Def.Probability.Process.HiddenMarkovSequence.Part2
import Theorem.Probability.Process.DiscreteHMM.Part2
open MeasureTheory


section

variable {Ω Y X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure Y] [CountableMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω} [IsProbabilityMeasure π] {x : ℕ → Ω → X} {y : ℕ → Ω → Y}

instance [h : IsDiscreteHMM π x y] (n m : ℤ) : SinglePSpace π (x[:n], y[:m]) :=
  Random.SinglePSpace.of.All_Measurable.All_Measurable h.measurable_x h.measurable_y

instance [h : IsDiscreteHMM π x y] (a b : ℤ) (j : ℕ) : SinglePSpace π (JointRandomSymbol x[a:b] (y j)) :=
  Random.SinglePSpace.of.Measurable.Measurable
    (Measurable.of_eval fun _ => h.measurable_x _) (h.measurable_y j)

-- y-only `SinglePSpace` instances: `x` cannot be inferred from them, so they are scoped and only
-- active after `open IsDiscreteHMM` (Lean then finds `x` from the hypothesis `h : IsDiscreteHMM π x y`).

end
