-- Carved from Lemma/Definitions/Def_HopfAlgebra_HopfKerHopf.lean: instance decls only.
-- Carved: defs+theorems -> Def.HopfAlgebra_HopfKerHopf; instances remain here
import Mathlib
import Lemma.HopfAlgebra.HopfKer
import Def.HopfAlgebra_HopfKerHopf


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped TensorProduct
open Coalgebra

universe u v w

namespace HopfAlgebra.HopfKerHopf


section Structure

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] (π : A →ₐc[R] B)
variable [Module.Flat R A] [Module.Flat R B] [Module.Flat R ↥(hopfKer π)]
variable [Coalgebra.IsCocomm R A]

noncomputable instance instCoalgebra : Coalgebra R ↥(hopfKer π) where
  comul := comulK π
  counit := counitK π
  coassoc := by
    ext s
    apply ι₃_injective π
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      ι₃_assoc_rTensor_comulK, ι₃_lTensor_comulK, ι₂_comulK]
    exact LinearMap.congr_fun (Coalgebra.coassoc (R := R) (A := A)) (s : A)
  rTensor_counit_comp_comul := by
    ext s
    have hinj : Function.Injective ((valL π).lTensor R) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul, valL_apply]
    rw [rTensor_counitK, ι₂_comulK, Coalgebra.rTensor_counit_comul]
  lTensor_counit_comp_comul := by
    ext s
    have hinj : Function.Injective ((valL π).rTensor R) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, LinearMap.rTensor_tmul,
      valL_apply]
    rw [lTensor_counitK, ι₂_comulK, Coalgebra.lTensor_counit_comul]

noncomputable instance instBialgebra : Bialgebra R ↥(hopfKer π) where
  counit_one := by rw [counit_coe]; simp
  mul_compr₂_counit := by
    ext a b
    exact (Bialgebra.counit_mul (R := R) (a : A) (b : A) : _)
  comul_one := by
    apply ι₂_injective π
    rw [ι₂_comul, ι₂_one]; simp
  mul_compr₂_comul := by
    ext a b
    apply ι₂_injective π
    change ι₂ π (Coalgebra.comul (R := R) (a * b)) = ι₂ π (Coalgebra.comul (R := R) a * Coalgebra.comul (R := R) b)
    rw [ι₂_mul, ι₂_comul, ι₂_comul, ι₂_comul, Subalgebra.coe_mul, Bialgebra.comul_mul]


noncomputable instance instHopfAlgebra : HopfAlgebra R ↥(hopfKer π) where
  antipode := antipodeK π
  mul_antipode_rTensor_comul := by
    ext s
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Subalgebra.coe_algebraMap]
    rw [val_mul'_rTensor_antipodeK, ι₂_comul, mul_antipode_rTensor_comul_apply, counit_coe]
  mul_antipode_lTensor_comul := by
    ext s
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Subalgebra.coe_algebraMap]
    rw [val_mul'_lTensor_antipodeK, ι₂_comul, mul_antipode_lTensor_comul_apply, counit_coe]


instance instIsCocomm : Coalgebra.IsCocomm R ↥(hopfKer π) where
  comm_comp_comul := by
    ext s
    apply ι₂_injective π
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ι₂_comm, ι₂_comul, Coalgebra.comm_comul]
end Structure

end HopfAlgebra.HopfKerHopf


