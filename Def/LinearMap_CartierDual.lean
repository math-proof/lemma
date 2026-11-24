module
public import Mathlib
public import Instance.HopfAlgebra_CartierDual
public import Structure.HopfAlgebra_CartierDual
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
open Coalgebra
open scoped TensorProduct


public section

universe u v

def CartierDual (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A] : Type (max u v) :=
  Module.Dual R A

namespace CartierDual

noncomputable section

section TransposeOfComul

variable (R : Type u) (A : Type v) [CommRing R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

omit [Coalgebra R A] in

end TransposeOfComul


section HeldLayer

variable (R : Type u) (A : Type v)


@[implicit_reducible] def coalgebraOfDualBialgebraAxioms [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] (h : DualBialgebraAxioms R A) :
    Coalgebra R (Module.Dual R A) where
  comul := dualComul R A
  counit := dualCounit R A
  coassoc := by
    apply LinearMap.ext
    intro φ
    simpa using h.coassoc_apply φ
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro φ
    simpa using h.rTensor_counit_comul φ
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro φ
    simpa using h.lTensor_counit_comul φ

end HeldLayer

end

noncomputable section

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

section PairingToolkit

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

def dualDistribEquiv₃ :
    Module.Dual R A ⊗[R] (Module.Dual R A ⊗[R] Module.Dual R A) ≃ₗ[R]
      Module.Dual R (A ⊗[R] (A ⊗[R] A)) :=
  (TensorProduct.congr (LinearEquiv.refl R (Module.Dual R A))
      (TensorProduct.dualDistribEquiv R A A)).trans
    (TensorProduct.dualDistribEquiv R A (A ⊗[R] A))

end PairingToolkit


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

@[implicit_reducible] def dualCoalgebraOfFiniteFree : Coalgebra R (Module.Dual R A) :=
  coalgebraOfDualBialgebraAxioms R A (dualBialgebraAxioms_of_finite_free R A)

end BialgebraBundle

section HopfDischarge

variable [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

end HopfDischarge

end

noncomputable section


section RingCarrier

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

@[reducible] def dualConvRing : Ring (Module.Dual R A) where
  __ := (inferInstance : AddCommMonoid (Module.Dual R A))
  __ := (inferInstance : AddCommGroup (Module.Dual R A))
  mul f g := dualMul R A (f ⊗ₜ[R] g)
  one := Coalgebra.counit (R := R) (A := A)
  mul_assoc := dualMul_assoc R A
  one_mul := dualMul_counit_tmul R A
  mul_one := dualMul_tmul_counit R A
  left_distrib f g h := by
    show dualMul R A (f ⊗ₜ[R] (g + h)) = dualMul R A (f ⊗ₜ[R] g) + dualMul R A (f ⊗ₜ[R] h)
    rw [TensorProduct.tmul_add, map_add]
  right_distrib f g h := by
    show dualMul R A ((f + g) ⊗ₜ[R] h) = dualMul R A (f ⊗ₜ[R] h) + dualMul R A (g ⊗ₜ[R] h)
    rw [TensorProduct.add_tmul, map_add]
  zero_mul f := by
    show dualMul R A ((0 : Module.Dual R A) ⊗ₜ[R] f) = 0
    rw [TensorProduct.zero_tmul, map_zero]
  mul_zero f := by
    show dualMul R A (f ⊗ₜ[R] (0 : Module.Dual R A)) = 0
    rw [TensorProduct.tmul_zero, map_zero]

@[reducible] def dualConvCommRing [IsCocomm R A] : CommRing (Module.Dual R A) where
  __ := dualConvRing R A
  mul_comm f g := by
    show dualMul R A (f ⊗ₜ[R] g) = dualMul R A (g ⊗ₜ[R] f)
    simp only [dualMul_tmul_eq_convMul]
    exact congrArg WithConv.ofConv (mul_comm (WithConv.toConv f) (WithConv.toConv g))

end RingCarrier

section AlgebraCarrier

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

attribute [local instance] dualConvRing

@[reducible] def dualConvAlgebra : Algebra R (Module.Dual R A) where
  toSMul := (inferInstance : SMul R (Module.Dual R A))
  algebraMap :=
    { toFun := fun r => dualUnit R A r
      map_one' := dualUnit_one R A
      map_mul' := fun r s => dualUnit_mul R A r s
      map_zero' := map_zero (dualUnit R A)
      map_add' := fun r s => map_add (dualUnit R A) r s }
  commutes' := fun r f => (dualMul_dualUnit_tmul R A r f).trans (dualMul_tmul_dualUnit R A f r).symm
  smul_def' := fun r f => (dualMul_dualUnit_tmul R A r f).symm

end AlgebraCarrier

section BialgebraPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]

@[reducible] def dualBialgebraOfFiniteFree : Bialgebra R (Module.Dual R A) :=
  Bialgebra.mk' R (Module.Dual R A)
    (dualCounit_counit R A)
    (fun {f g} => dualCounit_dualMul R A f g)
    (dualComul_counit_eq_tensorOne R A)
    (fun {f g} => dualComul_dualMul_eq_mul R A f g)

end BialgebraPackage

section HopfPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]

@[reducible] def dualHopfAlgebraOfFiniteFree : HopfAlgebra R (Module.Dual R A) where
  toBialgebra := dualBialgebraOfFiniteFree R A
  antipode := (HopfAlgebra.antipode R (A := A)).dualMap
  mul_antipode_rTensor_comul := dualConv_mul'_antipode_rTensor_dualComul R A
  mul_antipode_lTensor_comul := dualConv_mul'_antipode_lTensor_dualComul R A

end HopfPackage

end

noncomputable section


section CommBialgebraPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]

attribute [local instance] dualConvCommRing dualConvAlgebra dualCoalgebraOfFiniteFree

@[reducible] def dualCommBialgebraOfFiniteFree : Bialgebra R (Module.Dual R A) :=
  Bialgebra.mk' R (Module.Dual R A)
    (dualCounit_counit R A)
    (fun {f g} => dualCounit_dualMul R A f g)
    (dualComul_counit_eq_tensorOne R A)
    (fun {f g} => dualComul_dualMul_eq_mul R A f g)

end CommBialgebraPackage

section CommHopfPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]

attribute [local instance] dualConvCommRing dualConvAlgebra dualCoalgebraOfFiniteFree

@[reducible] def dualCommHopfAlgebraOfFiniteFree : HopfAlgebra R (Module.Dual R A) where
  toBialgebra := dualCommBialgebraOfFiniteFree R A
  antipode := (HopfAlgebra.antipode R (A := A)).dualMap
  mul_antipode_rTensor_comul := dualConv_mul'_antipode_rTensor_dualComul R A
  mul_antipode_lTensor_comul := dualConv_mul'_antipode_lTensor_dualComul R A

end CommHopfPackage

end

noncomputable section

section Instances

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

def toDual : CartierDual R A ≃ₗ[R] Module.Dual R A where
  toFun φ := φ
  invFun φ := φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def ofDual : Module.Dual R A ≃ₗ[R] CartierDual R A := (toDual R A).symm

variable {R A}

variable (R A)
variable [Module.Finite R A] [Module.Free R A]

variable {R A}

end Instances


end

end CartierDual
