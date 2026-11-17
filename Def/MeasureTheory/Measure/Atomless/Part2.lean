/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.MonotoneConvergence
public import Structure.MeasureTheory.Measure.Atomless

@[expose] public section

section

open MeasureTheory Set Filter Topology

namespace MeasureTheory

/-- The greedy piece chosen at a Sierpinski state. -/
noncomputable def sierpinskiPiece {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (U : SierpinskiState μ s t) : Set α :=
  Classical.choose (sierpinskiChoice ht U.hle)

end MeasureTheory
end
