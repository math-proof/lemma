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
import Theorem.MeasureTheory.OptimalTransport.Kantorovich.Part5


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
