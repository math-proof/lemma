/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.Order.Compact
public import Def.MeasureTheory.OptimalTransport.Kantorovich.Part3

public section

section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

theorem phiPlusPsi_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (z : X × Y) :
    phiPlusPsi d z = d.1 z.1 + d.2 z.2 := rfl

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
