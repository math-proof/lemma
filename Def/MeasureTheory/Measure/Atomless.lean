/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence


section

open MeasureTheory Set Filter Topology

namespace MeasureTheory

/-!
# Atomless measures

Basic API for atomless measures: restriction to measurable sets and the
Sierpinski theorem that every intermediate measure value is attained.
-/

/-- `μ` is atomless when every positive-measure measurable set contains a smaller
positive-measure measurable subset. -/
def IsAtomless {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop :=
  ∀ s, MeasurableSet s → 0 < μ s → ∃ t, t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s

/-- Admissible measures for the Sierpinski greedy step: measures of measurable pieces of
`s \ u` that fit in the remaining budget. -/
def sierpinskiAdm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (t : ENNReal) (u : Set α) : Set ENNReal :=
  { m | ∃ v, MeasurableSet v ∧ v ⊆ s \ u ∧ μ u + μ v ≤ t ∧ μ v = m }

/-- Capacity: supremum of admissible measures for the Sierpinski greedy step. -/
noncomputable def sierpinskiCap {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (t : ENNReal) (u : Set α) : ENNReal :=
  sSup (sierpinskiAdm μ s t u)

end MeasureTheory
end
