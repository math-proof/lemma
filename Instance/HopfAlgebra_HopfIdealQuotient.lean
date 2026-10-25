-- Carved from Lemma/Definitions/Def_HopfAlgebra_HopfIdealQuotient.lean: instance decls only.
import Mathlib
import Class.HopfAlgebra_HopfIdealQuotient

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv


section IsHopfIdeal'

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

instance Ideal.isHopfIdeal_bot : (⊥ : Ideal H).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  counit_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  antipode_mem x hx := by rw [(Ideal.mem_bot).1 hx]; simp

end IsHopfIdeal'

namespace HopfAlgebra

namespace HopfIdealQuotient

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]
variable (I : Ideal H) [hI : I.IsHopfIdeal' R]

instance instBialgebra : Bialgebra R (H ⧸ I) :=
  Bialgebra.ofAlgHom (comul R I) (counit R I) (coassoc R I) (rTensor_counit_comul R I)
    (lTensor_counit_comul R I)

instance instHopfAlgebra : HopfAlgebra R (H ⧸ I) :=
  HopfAlgebra.ofAlgHom (antipode R I) (mul_antipode_rTensor_comul R I)
    (mul_antipode_lTensor_comul R I)

instance instIsCocomm [Coalgebra.IsCocomm R H] : Coalgebra.IsCocomm R (H ⧸ I) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.comp_apply, coalgebra_comul_mk]
    conv_rhs => rw [← Coalgebra.comm_comp_comul R H]
    rw [LinearMap.comp_apply]
    generalize Coalgebra.comul (R := R) x = z
    induction z with
    | zero => simp
    | tmul a b => simp
    | add z w hz hw => simp only [map_add, hz, hw]

end HopfIdealQuotient

section Maps

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

variable {A : Type*} [CommRing A] [Algebra R A]

instance finiteType_quotient (I : Ideal H) [Algebra.FiniteType R H] :
    Algebra.FiniteType R (H ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)

instance flat_quotient_bot [Module.Flat R H] : Module.Flat R (H ⧸ (⊥ : Ideal H)) :=
  Module.Flat.of_linearEquiv (quotientBotAlgEquiv R (H := H)).toLinearEquiv

end Maps

end HopfAlgebra

end
