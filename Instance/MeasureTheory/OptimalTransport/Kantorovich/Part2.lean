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
public import Theorem.MeasureTheory.OptimalTransport.Kantorovich.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- The first marginal of a finite measure is finite. -/
instance isFiniteMeasure_map_fst
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.map Prod.fst) :=
  Measure.isFiniteMeasure_map μ Prod.fst

/-- The second marginal of a finite measure is finite. -/
instance isFiniteMeasure_map_snd
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.map Prod.snd) :=
  Measure.isFiniteMeasure_map μ Prod.snd

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
