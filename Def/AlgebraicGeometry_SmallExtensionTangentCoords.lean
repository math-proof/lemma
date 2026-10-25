import Mathlib
import Def.AlgebraicGeometry_SmallExtensionPairTangent

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

variable (T') in

def vPart : thickening T' V C →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V :=
  TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)

def tensorToDualHom (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
    (W : Type u) [AddCommGroup W] [Module k W] :
    M ⊗[k] W →ₗ[k] (Module.Dual k W →ₗ[k] M) :=
  TensorProduct.lift
    (LinearMap.mk₂ k (fun (m : M) (w : W) => (LinearMap.smulRight (Module.Dual.eval k W w) m : Module.Dual k W →ₗ[k] M))
      (fun m₁ m₂ w => by ext ξ; simp)
      (fun c m w => by ext ξ; simp [smul_smul, mul_comm])
      (fun m w₁ w₂ => by ext ξ; simp [add_smul])
      (fun c m w => by ext ξ; simp [smul_smul]))


variable (T') in

def tangentCoords {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) :
    Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C) :=
  tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C (φ a))

end AlgebraicGeometry.SmallExtension

end
