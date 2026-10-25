/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Order.Compact
import Theorem.MeasureTheory.OptimalTransport.Kantorovich.Part4


section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- The affine map whose sublevel set (at `0`) is the separating set. -/
noncomputable def sepMap
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    ((W →ᵇ ℝ) × ℝ) → (W →ᵇ ℝ) := fun p => p.1 - cb - (p.2 - t) • 1

/-- The separating open convex set: pairs strictly below the cost-shifted threshold. -/
noncomputable def sepSet
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    Set ((W →ᵇ ℝ) × ℝ) := sepMap cb t ⁻¹' {w | ∀ z, w z < 0}

/-- The graph of the dual objective over the sum map, as a submodule. -/
noncomputable def graphSub
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Submodule ℝ (((X × Y) →ᵇ ℝ) × ℝ) :=
  LinearMap.range (LinearMap.prod PhiLM (dualValLM μ ν))

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
