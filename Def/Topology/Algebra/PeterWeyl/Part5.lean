module
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Theorem.Topology.Algebra.PeterWeyl.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory

open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

section PWHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The set of bounded versions of `T0 f` for `‖f‖ ≤ 1`. -/
noncomputable def pwA (k : C(G, ℂ)) : Set (G →ᵇ ℂ) :=
  (ContinuousMap.isometryEquivBoundedOfCompact G ℂ) ''
    ((fun f => pwT0Map (G := G) k f) '' Metric.closedBall 0 1)

end PWHelpers
end MathlibExt.Topology.Algebra.PeterWeylWanted
end
