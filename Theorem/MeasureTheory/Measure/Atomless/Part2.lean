/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.MonotoneConvergence
public import Def.MeasureTheory.Measure.Atomless.Part2

public section

section

open MeasureTheory Set Filter Topology

namespace MeasureTheory

/-- Specification of the greedy piece. -/
theorem sierpinskiPiece_spec {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (U : SierpinskiState μ s t) :
    MeasurableSet (sierpinskiPiece ht U) ∧
      sierpinskiPiece ht U ⊆ s \ U.u ∧
      μ U.u + μ (sierpinskiPiece ht U) ≤ t ∧
      sierpinskiCap μ s t U.u / 2 ≤ μ (sierpinskiPiece ht U) :=
  Classical.choose_spec (sierpinskiChoice ht U.hle)

end MeasureTheory
end
