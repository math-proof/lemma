/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence
import Theorem.MeasureTheory.Measure.Atomless


section

open MeasureTheory Set Filter Topology

namespace MeasureTheory

/-- State for the Sierpinski greedy recursion: a measurable subset of `s` within budget. -/
structure SierpinskiState {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (t : ENNReal) where
  u : Set α
  hsub : u ⊆ s
  hmeas : MeasurableSet u
  hle : μ u ≤ t

end MeasureTheory
end
