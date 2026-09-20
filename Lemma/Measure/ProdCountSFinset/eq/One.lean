import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Prod
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
-- given
  (a : α)
  (b : β) :
-- imply
  ((Measure.count : Measure α).prod (Measure.count : Measure β)) {(a, b)} = 1 := by
-- proof
  have : ({(a, b)} : Set (α × β)) = ({a} : Set α) ×ˢ ({b} : Set β) := by
    ext ⟨x, y⟩
    simp [Prod.mk.injEq]
  rw [this, Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, mul_one]


-- created on 2026-09-20
