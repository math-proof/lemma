import Lemma.Random.SinglePSpace.of.Measurable
import Instance.Probability.Rv.Part2
import Lemma.Measure.Count.eq.ProdCountS
import Syntax.Probability.Expectation.Elab
open MeasureTheory Random


/--
The joint law of two measurable discrete random variables has a density.
If `x : Ω → α` and `y : Ω → β` are measurable and `α`, `β` carry the counting measure
(`[CountableMeasure α]` / `[CountableMeasure β]`, countable, with measurable singletons),
then the pair `(x, y)` spans a `SinglePSpace π` with respect to the product reference measure.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α] [CountableMeasure β]
  [Countable α] [MeasurableSingletonClass α] [Countable β] [MeasurableSingletonClass β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β}
-- given
  (hx : Measurable x)
  (hy : Measurable y) :
-- imply
  SinglePSpace π (x, y) := by
-- proof
  have : CountableMeasure (α × β) := instCountableMeasureProd
  have hμ : ReferenceMeasure.measure (α := α × β) = Measure.count := by
    change (ReferenceMeasure.measure (α := α)).prod ReferenceMeasure.measure = Measure.count
    rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count,
      ← Measure.Count.eq.ProdCountS]
  have hacc : π.map (x, y) ≪ ReferenceMeasure.measure := by
    rw [hμ]
    intro s hs0
    rw [Measure.count_eq_zero_iff.mp hs0]
    apply measure_empty
  let q := (π.map (x, y)).rnDeriv ReferenceMeasure.measure
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := (hx.prodMk hy).aemeasurable
    exists_distribution :=
      ⟨q, Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _ hacc).symm⟩
  }

-- created on 2026-10-22
-- updated on 2026-11-16
