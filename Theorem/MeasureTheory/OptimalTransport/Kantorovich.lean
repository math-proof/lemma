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
import Def.MeasureTheory.OptimalTransport.Kantorovich


section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- A continuous real function on a compact space is integrable w.r.t. any finite measure. -/
lemma integrable_continuous_compact
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X → ℝ) (hf : Continuous f) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f μ := by
  rw [← integrableOn_univ]
  exact ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn

/-- Weak duality: any dual-feasible value is below any primal (coupling) value. -/
lemma dual_le_primal_of_isCoupling
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) (φ : X → ℝ) (ψ : Y → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hle : ∀ x y, φ x + ψ y ≤ c (x, y))
    (π : ProbabilityMeasure (X × Y)) (hπ : IsCoupling μ ν π) :
    (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)
      ≤ ∫ p, c p ∂(π : Measure (X × Y)) := by
  obtain ⟨hμ, hν⟩ := hπ
  have hφπ : Integrable (fun p : X × Y => φ p.1) (π : Measure (X × Y)) :=
    integrable_continuous_compact _ (hφ.comp continuous_fst) _
  have hψπ : Integrable (fun p : X × Y => ψ p.2) (π : Measure (X × Y)) :=
    integrable_continuous_compact _ (hψ.comp continuous_snd) _
  have hcπ : Integrable c (π : Measure (X × Y)) :=
    integrable_continuous_compact _ hc _
  have eφ : (∫ x, φ x ∂(μ : Measure X))
      = ∫ p : X × Y, φ p.1 ∂(π : Measure (X × Y)) := by
    rw [hμ, integral_map measurable_fst.aemeasurable hφ.aestronglyMeasurable]
  have eψ : (∫ y, ψ y ∂(ν : Measure Y))
      = ∫ p : X × Y, ψ p.2 ∂(π : Measure (X × Y)) := by
    rw [hν, integral_map measurable_snd.aemeasurable hψ.aestronglyMeasurable]
  rw [eφ, eψ, ← integral_add hφπ hψπ]
  exact integral_mono_ae (hφπ.add hψπ) hcπ
    (Filter.Eventually.of_forall fun p => hle p.1 p.2)

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
