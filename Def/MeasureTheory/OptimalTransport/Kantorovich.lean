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
