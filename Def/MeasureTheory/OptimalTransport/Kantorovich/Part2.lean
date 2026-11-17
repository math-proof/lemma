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
public import Theorem.MeasureTheory.OptimalTransport.Kantorovich

@[expose] public section

section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- A continuous real function on a nonempty compact space as a bounded continuous function. -/
noncomputable def mkBCF
    {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
    (f : W → ℝ) (hf : Continuous f) : W →ᵇ ℝ where
  toContinuousMap := ⟨f, hf⟩
  map_bounded' := by
    obtain ⟨z₁, -, hz₁⟩ :=
      isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
    obtain ⟨z₀, -, hz₀⟩ :=
      isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
    refine ⟨|f z₁| + |f z₀|, fun x y => ?_⟩
    rw [dist_eq_norm, Real.norm_eq_abs]
    have hx1 : f x ≤ f z₁ := isMaxOn_iff.mp hz₁ x (Set.mem_univ _)
    have hx0 : f z₀ ≤ f x := isMinOn_iff.mp hz₀ x (Set.mem_univ _)
    have hy1 : f y ≤ f z₁ := isMaxOn_iff.mp hz₁ y (Set.mem_univ _)
    have hy0 : f z₀ ≤ f y := isMinOn_iff.mp hz₀ y (Set.mem_univ _)
    have g1 : f z₁ ≤ |f z₁| := le_abs_self _
    have g2 : -(f z₀) ≤ |f z₀| := neg_le_abs _
    rw [abs_le]
    constructor <;> linarith

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
