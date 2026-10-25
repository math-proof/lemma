import Mathlib
import Instance.HopfAlgebra_CartierDual

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Coalgebra
open scoped TensorProduct

universe u v


namespace CartierDual

noncomputable section

section TransposeOfComul

variable (R : Type u) (A : Type v) [CommRing R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

omit [Coalgebra R A] in


def dualMul : Module.Dual R A ⊗[R] Module.Dual R A →ₗ[R] Module.Dual R A :=
  (Coalgebra.comul (R := R) (A := A)).dualMap ∘ₗ TensorProduct.dualDistrib R A A


end TransposeOfComul

section TransposeOfMul

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]


def dualComul : Module.Dual R A →ₗ[R] Module.Dual R A ⊗[R] Module.Dual R A :=
  (TensorProduct.dualDistribEquiv R A A).symm.toLinearMap ∘ₗ (LinearMap.mul' R A).dualMap


end TransposeOfMul

section UnitCounit

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

def dualOneEquiv : Module.Dual R R ≃ₗ[R] R := LinearMap.ringLmapEquivSelf R R R


def dualCounit : Module.Dual R A →ₗ[R] R :=
  (dualOneEquiv R).toLinearMap ∘ₗ (Algebra.linearMap R A).dualMap


def dualUnit : R →ₗ[R] Module.Dual R A :=
  (Coalgebra.counit (R := R) (A := A)).dualMap ∘ₗ (dualOneEquiv R).symm.toLinearMap


end UnitCounit

section DerivableAxioms

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]


variable [Module.Finite R A] [Module.Free R A]


end DerivableAxioms

section HeldLayer

variable (R : Type u) (A : Type v)

structure DualBialgebraAxioms [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] : Prop where

  coassoc_apply : ∀ φ : Module.Dual R A,
    TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
        ((dualComul R A).rTensor (Module.Dual R A) (dualComul R A φ)) =
      (dualComul R A).lTensor (Module.Dual R A) (dualComul R A φ)

  rTensor_counit_comul : ∀ φ : Module.Dual R A,
    (dualCounit R A).rTensor (Module.Dual R A) (dualComul R A φ) = (1 : R) ⊗ₜ[R] φ

  lTensor_counit_comul : ∀ φ : Module.Dual R A,
    (dualCounit R A).lTensor (Module.Dual R A) (dualComul R A φ) = φ ⊗ₜ[R] (1 : R)

  dualComul_dualMul : ∀ f g : Module.Dual R A,
    dualComul R A (dualMul R A (f ⊗ₜ[R] g)) =
      TensorProduct.map (dualMul R A) (dualMul R A)
        (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
          (Module.Dual R A) (Module.Dual R A) ((dualComul R A f) ⊗ₜ[R] (dualComul R A g)))

structure DualHopfAxioms [CommRing R] [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Free R A] : Prop extends DualBialgebraAxioms R A where

  mul_antipode_rTensor_comul : ∀ φ : Module.Dual R A,
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ)

  mul_antipode_lTensor_comul : ∀ φ : Module.Dual R A,
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ)


end HeldLayer

end

noncomputable section

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

section PairingToolkit

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in


end PairingToolkit

section Coassoc

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]


end Coassoc

section CounitLaws

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in


end CounitLaws

section Multiplicativity

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in


end Multiplicativity

section BialgebraBundle

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]


end BialgebraBundle

section HopfDischarge

variable [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in


end HopfDischarge

end

noncomputable section

section ConvIdentities

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]


end ConvIdentities

section RingCarrier

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]


end RingCarrier

section AlgebraCarrier

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]


end AlgebraCarrier

section BialgebraPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]


end BialgebraPackage

section HopfPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]


end HopfPackage

end

noncomputable section

section PairingSwap

variable (R : Type u) (A : Type v) [CommRing R] [AddCommMonoid A] [Module R A]


end PairingSwap

section Cocomm

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]


end Cocomm

section CommBialgebraPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]


end CommBialgebraPackage

section CommHopfPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]


end CommHopfPackage

end

noncomputable section

section Instances

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]


variable {R A}


variable (R A)
variable [Module.Finite R A] [Module.Free R A]


variable {R A}


end Instances

section HopfInstance

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]

variable {R A}


end HopfInstance

section BidualSanity
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]
end BidualSanity

section BidualSanityHopf
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]
end BidualSanityHopf

end

end CartierDual

namespace MonoidAlgebra

end MonoidAlgebra

section
variable (R : Type*) [CommRing R] (Γ : Type*) [CommGroup Γ] [Fintype Γ]
end
