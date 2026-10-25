/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/LyapunovConvexity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorem.MeasureTheory.Measure.Atomless.Part3
import Lemma.Measure.Atomless
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences


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
