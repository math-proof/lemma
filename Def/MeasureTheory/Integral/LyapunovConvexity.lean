/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/LyapunovConvexity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Theorem.MeasureTheory.Measure.Atomless.Part3
public import Theorem.Measure.Atomless
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Sequences

@[expose] public section

section

open MeasureTheory Set Filter Topology

open scoped RealInnerProductSpace

namespace MathlibExt.MeasureTheory.Integral.LyapunovConvexityWanted

/-!
# Lyapunov convexity theorem

Records Lyapunov's convexity theorem for the range of a finite-dimensional vector measure.
-/

/-- Set of integrals of `f` over measurable sets. -/
noncomputable def lyapunovRange {α : Type*} [MeasurableSpace α] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (f : α → E) :
    Set E :=
  { y | ∃ (s : Set α), MeasurableSet s ∧ y = ∫ x in s, f x ∂μ }

/-- The undecided set of a relaxed control: points where `g` is strictly
between 0 and 1. -/
def bangBangUndecided {α : Type*} (g : α → ℝ) : Set α :=
  { x | 0 < g x ∧ g x < 1 }

end MathlibExt.MeasureTheory.Integral.LyapunovConvexityWanted
end
