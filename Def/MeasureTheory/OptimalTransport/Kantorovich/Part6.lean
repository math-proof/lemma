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
import Instance.MeasureTheory.OptimalTransport.Kantorovich.Part2


section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- Pullback of a compactly supported function along `Prod.fst`. -/
noncomputable def fstCC
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (f : C_c(X, ℝ)) : C_c(X × Y, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun z => f z.1, f.toBoundedContinuousFunction.continuous.comp continuous_fst⟩

/-- Pullback of a compactly supported function along `Prod.snd`. -/
noncomputable def sndCC
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (g : C_c(Y, ℝ)) : C_c(X × Y, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun z => g z.2, g.toBoundedContinuousFunction.continuous.comp continuous_snd⟩

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
