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
import Def.MeasureTheory.OptimalTransport.Kantorovich.Part4


section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- Dual values are bounded above (by any primal value). -/
theorem dual_bddAbove
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    BddAbove {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  refine ⟨∫ p, c p ∂((μ.prod ν) : Measure (X × Y)), ?_⟩
  rintro r ⟨φ, ψ, hfeas, rfl⟩
  obtain ⟨hφ, hψ, hle⟩ := hfeas
  exact dual_le_primal_of_isCoupling μ ν c hc φ ψ hφ hψ hle _ (isCoupling_prod μ ν)

/-- Primal values are bounded below (by the minimum of `c`). -/
theorem primal_bddBelow
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    BddBelow (primalValues μ ν c) := by
  obtain ⟨p₀, -, hp₀⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  refine ⟨c p₀, ?_⟩
  rintro q ⟨π, hπ, rfl⟩
  have hmin : ∀ z, c p₀ ≤ c z := fun z => isMinOn_iff.mp hp₀ z (Set.mem_univ _)
  have h1 : Integrable c (π : Measure (X × Y)) :=
    integrable_continuous_compact _ hc _
  have h2 : Integrable (fun _ : X × Y => c p₀) (π : Measure (X × Y)) :=
    integrable_const _
  have hle := integral_mono_ae h2 h1 (Filter.Eventually.of_forall hmin)
  simpa using hle

/-- Key estimate: shifting a pair down by an upper bound on the violation stays
below the dual supremum. -/
theorem key_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c)
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (m : ℝ) (hm : ∀ z, (PhiLM d) z - c z ≤ m) :
    (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ≤ sSup {r : ℝ | ∃ φ : X → ℝ,
      ∃ ψ : Y → ℝ, DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  have hbdd := dual_bddAbove μ ν c hc
  have hmem : (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ∈ {r : ℝ | ∃ φ : X → ℝ,
      ∃ ψ : Y → ℝ, DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
    refine ⟨⇑(d.1 - BoundedContinuousFunction.const X m), ⇑d.2,
      ⟨(d.1 - BoundedContinuousFunction.const X m).continuous, d.2.continuous, ?_⟩, ?_⟩
    · intro x y
      have h := hm (x, y)
      rw [PhiLM_apply] at h
      have hc1 : (d.1 - BoundedContinuousFunction.const X m) x = d.1 x - m := rfl
      rw [hc1]
      linarith
    · have hint1 : Integrable (fun x => d.1 x) (μ : Measure X) :=
        integrable_continuous_compact _ d.1.continuous _
      have hcm : Integrable (fun _ : X => m) (μ : Measure X) := integrable_const _
      have eφ : (∫ x, (d.1 - BoundedContinuousFunction.const X m) x ∂(μ : Measure X))
          = (∫ x, d.1 x ∂(μ : Measure X)) - m := by
        have e : (fun x => (d.1 - BoundedContinuousFunction.const X m) x)
            = (fun x => d.1 x - m) := rfl
        rw [e, integral_sub hint1 hcm]
        congr 1
        simp
      have hval : (dualValLM (μ : Measure X) (ν : Measure Y) d)
          = (∫ x, d.1 x ∂(μ : Measure X)) + ∫ y, d.2 y ∂(ν : Measure Y) := rfl
      rw [hval, eφ]
      ring
  exact le_csSup hbdd hmem

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
