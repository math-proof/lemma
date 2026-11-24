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
public import Instance.MeasureTheory.OptimalTransport.Kantorovich.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
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
