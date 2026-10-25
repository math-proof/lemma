/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence
import Structure.MeasureTheory.Measure.Atomless


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
