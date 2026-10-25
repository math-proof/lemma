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

section OpenStabilizer

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*}

abbrev HasOpenStabilizer (G : Type*) {M : Type*} [Group G] [TopologicalSpace G] [MulAction G M]
    (v : M) : Prop :=
  IsOpen ((MulAction.stabilizer G v : Subgroup G) : Set G)

variable [MulAction G M]

end OpenStabilizer

section Witness

end Witness

section MeasureCoeff

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]


end MeasureCoeff

section FiniteRangeIntegral

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]


end FiniteRangeIntegral

section Integrand

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

end Integrand

section HeckeSmul

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]


end HeckeSmul

section Idempotent

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {G : Type*}


end Idempotent

section Projection

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]


end Projection

end TestFunctionAction
