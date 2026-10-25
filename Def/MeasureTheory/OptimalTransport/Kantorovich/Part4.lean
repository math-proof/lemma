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
import Theorem.MeasureTheory.OptimalTransport.Kantorovich.Part3


section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- The sum map as a linear map into bounded continuous functions on the product. -/
noncomputable def PhiLM
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] :
    ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ((X × Y) →ᵇ ℝ) where
  toFun := phiPlusPsi
  map_add' d e := by
    apply BoundedContinuousFunction.ext
    intro z
    have h1 : (d + e).1 z.1 = d.1 z.1 + e.1 z.1 := rfl
    have h2 : (d + e).2 z.2 = d.2 z.2 + e.2 z.2 := rfl
    simp only [phiPlusPsi_apply, BoundedContinuousFunction.add_apply, h1, h2]
    ring
  map_smul' c d := by
    apply BoundedContinuousFunction.ext
    intro z
    have h1 : (c • d).1 z.1 = c • d.1 z.1 := rfl
    have h2 : (c • d).2 z.2 = c • d.2 z.2 := rfl
    simp only [phiPlusPsi_apply, BoundedContinuousFunction.smul_apply, h1, h2, smul_add,
      RingHom.id_apply]

/-- The dual objective as a linear map on pairs of bounded continuous functions. -/
noncomputable def dualValLM
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ℝ where
  toFun d := (∫ x, d.1 x ∂μ) + ∫ y, d.2 y ∂ν
  map_add' d e := by
    have hφ1 : Integrable (fun x => d.1 x) μ :=
      integrable_continuous_compact _ d.1.continuous _
    have hφ2 : Integrable (fun x => e.1 x) μ :=
      integrable_continuous_compact _ e.1.continuous _
    have hψ1 : Integrable (fun y => d.2 y) ν :=
      integrable_continuous_compact _ d.2.continuous _
    have hψ2 : Integrable (fun y => e.2 y) ν :=
      integrable_continuous_compact _ e.2.continuous _
    have e1 : (fun x => (d + e).1 x) = (fun x => d.1 x + e.1 x) := rfl
    have e2 : (fun y => (d + e).2 y) = (fun y => d.2 y + e.2 y) := rfl
    change (∫ x, (d + e).1 x ∂μ) + ∫ y, (d + e).2 y ∂ν = _
    rw [e1, e2, integral_add hφ1 hφ2, integral_add hψ1 hψ2]
    ring
  map_smul' c d := by
    have e1 : (fun x => (c • d).1 x) = (fun x => c • d.1 x) := rfl
    have e2 : (fun y => (c • d).2 y) = (fun y => c • d.2 y) := rfl
    change (∫ x, (c • d).1 x ∂μ) + ∫ y, (c • d).2 y ∂ν = _
    simp only [e1, e2, integral_smul, smul_add, RingHom.id_apply]

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
