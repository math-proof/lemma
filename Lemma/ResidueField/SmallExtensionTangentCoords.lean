import Mathlib
import Def.AlgebraicGeometry_SmallExtensionPairTangent
import Def.AlgebraicGeometry_SmallExtensionTangentCoords

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

universe u

open TensorProduct IsLocalRing

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]


@[simp] theorem tensorToDualHom_tmul (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
    (W : Type u) [AddCommGroup W] [Module k W] (m : M) (w : W) (ξ : Module.Dual k W) :
    tensorToDualHom k M W (m ⊗ₜ w) ξ = ξ w • m := by
  simp [tensorToDualHom]


theorem tangentCoords_apply {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) (ξ : Module.Dual (ResidueField T') V) :
    tangentCoords T' V C φ a ξ = tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C (φ a)) ξ := rfl

theorem tangentCoords_add {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a b : A) :
    tangentCoords T' V C φ (a + b) = tangentCoords T' V C φ a + tangentCoords T' V C φ b := by
  unfold tangentCoords
  rw [φ.map_add, LinearMap.map_add, LinearMap.map_add]

end AlgebraicGeometry.SmallExtension

end
