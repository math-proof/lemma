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

@[expose] public section

section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-!
# Kantorovich duality on compact metric spaces

Strong Kantorovich duality on products of nonempty compact
metric Borel probability spaces with continuous cost.
-/

/-- Coupling of `μ` and `ν`: prob. measure on `X × Y` with marginals `μ`, `ν`. -/
def IsCoupling {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (π : ProbabilityMeasure (X × Y)) : Prop :=
  (μ : Measure X) = (π : Measure (X × Y)).map Prod.fst ∧
    (ν : Measure Y) = (π : Measure (X × Y)).map Prod.snd

/-- Values of `∫ c dπ` over couplings `π` of `μ`, `ν`. -/
def primalValues {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) : Set ℝ :=
  {r : ℝ | ∃ π : ProbabilityMeasure (X × Y),
    IsCoupling μ ν π ∧ r = ∫ p, c p ∂(π : Measure (X × Y))}

/-- Dual feasibility: continuous `φ`, `ψ` with `φ x + ψ y ≤ c (x,y)`. -/
def DualFeasible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (c : X × Y → ℝ) (φ : X → ℝ) (ψ : Y → ℝ) : Prop :=
  Continuous φ ∧ Continuous ψ ∧ ∀ x y, φ x + ψ y ≤ c (x, y)

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
