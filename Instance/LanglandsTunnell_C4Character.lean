-- Carved from Lemma/Definitions/Def_LanglandsTunnell_C4Character.lean: instance decls only.
import Instance.LanglandsTunnell_QuatH

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain


section TowerInstances

open LanglandsTunnell

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))


noncomputable instance algebra_fixFldC8H_fixFldC4H :
    Algebra ↥(fixFld (c8H e)) ↥(fixFld (c4H e)) :=
  (IntermediateField.inclusion (fixFld_c8H_le_fixFld_c4H e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldC8H_fixFldC4H :
    IsScalarTower ℚ ↥(fixFld (c8H e)) ↥(fixFld (c4H e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldC8H_fixFldC4H_L :
    IsScalarTower ↥(fixFld (c8H e)) ↥(fixFld (c4H e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_c8H_le_fixFld_c4H e) x).symm)


noncomputable instance algebra_fixFldQuatH_fixFldC4H :
    Algebra ↥(fixFld (quatH e)) ↥(fixFld (c4H e)) :=
  (IntermediateField.inclusion (fixFld_quatH_le_fixFld_c4H e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldQuatH_fixFldC4H :
    IsScalarTower ℚ ↥(fixFld (quatH e)) ↥(fixFld (c4H e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldQuatH_fixFldC4H_L :
    IsScalarTower ↥(fixFld (quatH e)) ↥(fixFld (c4H e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_quatH_le_fixFld_c4H e) x).symm)

end TowerInstances


end LanglandsTunnell.P2

end
