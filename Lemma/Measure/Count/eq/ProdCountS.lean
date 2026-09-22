import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Prod
import Lemma.Measure.ProdCountSFinset.eq.One
open MeasureTheory Measure


@[main, comm]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
-- imply
  (count : Measure (α × β)) = (count : Measure α).prod (count : Measure β) := by
-- proof
  refine Measure.ext_iff_singleton.mpr fun z ↦ ?_
  rw [count_singleton, ProdCountSFinset.eq.One]


-- created on 2026-09-20
