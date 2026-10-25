import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Module.BigOperators

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace TestFunctionAction


section MeasureCoeff

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]

noncomputable def measureCoeff (μ : Measure X) (s : Set X) : 𝕜 :=
  algebraMap ℝ 𝕜 (μ s).toReal

end MeasureCoeff

section FiniteRangeIntegral

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

open Classical in
noncomputable def finiteRangeIntegral (μ : Measure X) (F : X → V) : V :=
  if h : (Set.range F).Finite then
    ∑ w ∈ h.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w
  else 0

end FiniteRangeIntegral


section HeckeSmul

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

noncomputable def heckeSmul (μ : Measure G) (f : G → 𝕜) (v : V) : V :=
  finiteRangeIntegral 𝕜 μ fun g => f g • g • v

end HeckeSmul

section Idempotent

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {G : Type*}

noncomputable def heckeIdempotent [MeasurableSpace G] (μ : Measure G) (K : Set G) : G → 𝕜 :=
  K.indicator fun _ => algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹

end Idempotent

section Projection

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

variable (𝕜) in
def fixedPointsSubmodule (K : Subgroup G) : Submodule 𝕜 V where
  carrier := {v : V | ∀ k ∈ K, k • v = v}
  zero_mem' := fun k _ => smul_zero k
  add_mem' := by
    intro v w hv hw k hk
    rw [smul_add, hv k hk, hw k hk]
  smul_mem' := by
    intro c v hv k hk
    rw [smul_comm, hv k hk]

variable (𝕜) in
def augmentationSubmodule (K : Subgroup G) : Submodule 𝕜 V :=
  Submodule.span 𝕜 {x : V | ∃ k ∈ K, ∃ u : V, k • u - u = x}

end Projection

end TestFunctionAction
