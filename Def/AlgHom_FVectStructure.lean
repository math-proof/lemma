module

public import Mathlib
public import Structure.HopfAlgebra_FVectStructure

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

universe u v w x

namespace HopfAlgebra


namespace FVectStructure

variable {F : Type w} [Field F] {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
variable (σ : FVectStructure F R H)

noncomputable def addChar : AddChar F (WithConv (H →ₐ[R] H)) where
  toFun a := WithConv.toConv (σ.act a : H →ₐ[R] H)
  map_zero_eq_one' := σ.act_zero
  map_add_eq_mul' := σ.act_add

noncomputable def unitsAct (a : Fˣ) : H ≃ₐc[R] H :=
  BialgEquiv.ofBialgHom (σ.act a) (σ.act (a⁻¹ : Fˣ)) (σ.act_comp_act_inv a) (σ.act_inv_comp_act a)

end FVectStructure

def IsFCompatible {F : Type w} [Field F] {R : Type u} [CommRing R]
    {H : Type v} [CommRing H] [Bialgebra R H] {H' : Type x} [CommRing H'] [Bialgebra R H']
    (σ : FVectStructure F R H) (σ' : FVectStructure F R H') (u : H →ₐc[R] H') : Prop :=
  ∀ a : F, u.comp (σ.act a) = (σ'.act a).comp u

namespace IsFCompatible

variable {F : Type w} [Field F] {R : Type u} [CommRing R]
    {H : Type v} [CommRing H] [Bialgebra R H] {H' : Type x} [CommRing H'] [Bialgebra R H']
    {H'' : Type*} [CommRing H''] [Bialgebra R H'']

end IsFCompatible

namespace FVectStructure

variable (F : Type w) [Field F] (R : Type u) [CommRing R]

noncomputable def addMonoidAlgebra : FVectStructure F R (AddMonoidAlgebra R F) where
  act a := AddMonoidAlgebra.mapDomainBialgHom R (AddMonoidHom.mulLeft a)
  act_one := by
    apply BialgHom.coe_algHom_injective
    refine AddMonoidAlgebra.algHom_ext (fun x => ?_) (Subsingleton.elim _ _)
    simp
  act_mul a b := by
    apply BialgHom.coe_algHom_injective
    refine AddMonoidAlgebra.algHom_ext (fun x => ?_) (Subsingleton.elim _ _)
    simp [mul_assoc]
  act_zero := by
    congr 1
    refine AddMonoidAlgebra.algHom_ext (fun x => ?_) (Subsingleton.elim _ _)
    simp
  act_add a b := by
    rw [AlgHom.convMul_def]
    congr 1
    refine AddMonoidAlgebra.algHom_ext (fun x => ?_) (Subsingleton.elim _ _)
    simp [AddMonoidAlgebra.single_mul_single, add_mul]

end FVectStructure

end HopfAlgebra

end
