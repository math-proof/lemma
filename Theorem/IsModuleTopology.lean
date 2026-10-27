import Mathlib
import Class.Mathlib_IsModuleTopology
import Def.IsModuleTopology


namespace IsModuleTopology

section semiring_algebra

open scoped TensorProduct

@[continuity, fun_prop]
theorem continuous_mul'
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) :=
  continuous_bilinear_of_finite_left (LinearMap.mul R D)

end semiring_algebra

section ring_algebra

open scoped TensorProduct

variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

include R in
@[continuity, fun_prop]
theorem continuous_mul : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
  letI : TopologicalSpace (D ⊗[R] D) := moduleTopology R _
  haveI : IsModuleTopology R (D ⊗[R] D) := { eq_moduleTopology' := rfl }
  convert continuous_bilinear_of_finite_left <| (LinearMap.mul R D : D →ₗ[R] D →ₗ[R] D)
  exact (LinearMap.mul_apply' _ _).symm

end ring_algebra

@[simp]
theorem continuousAlgEquivOfIsBiscalar_apply {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S]
    [Algebra S A] [Algebra S B] [Algebra S' A] [Algebra S' B]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace S'] [IsModuleTopology S' A]
    [IsModuleTopology S' B] (e : A ≃ₐ[S] B) [IsBiscalar S S' e.toAlgHom] (a : A) :
    continuousAlgEquivOfIsBiscalar S' e a = e a :=
  rfl

end IsModuleTopology
