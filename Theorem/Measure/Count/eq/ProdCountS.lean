module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Prod
import Theorem.Measure.ProdCountSFinset.eq.One
public import Initialize.Tactic.Attr.Basic

public section

open MeasureTheory Measure


@[comm]
public theorem Measure.Count.eq.ProdCountS
  [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
-- imply
  (count : Measure (α × β)) = (count : Measure α).prod (count : Measure β) := by
-- proof
  refine Measure.ext_iff_singleton.mpr fun z ↦ ?_
  rw [count_singleton, ProdCountSFinset.eq.One]


-- created on 2026-09-20
