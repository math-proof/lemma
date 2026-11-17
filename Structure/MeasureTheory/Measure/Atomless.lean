/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.MonotoneConvergence
public import Theorem.MeasureTheory.Measure.Atomless


public section

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
