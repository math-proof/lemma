-- Carved from Lemma/Definitions/Def_LanglandsTunnell_C8Tower.lean: instance decls only.
import Lemma.LanglandsTunnell.C8Character
import Instance.LanglandsTunnell_QuatH
import Lemma.LanglandsTunnell.C8Tower

set_option autoImplicit false

namespace LanglandsTunnell


section TowerInstances

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

noncomputable instance algebra_fixFldSylowH_fixFldC8H :
    Algebra ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) :=
  (IntermediateField.inclusion (fixFld_sylowH_le_fixFld_c8H e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldSylowH_fixFldC8H :
    IsScalarTower ℚ ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldSylowH_fixFldC8H_L :
    IsScalarTower ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_sylowH_le_fixFld_c8H e) x).symm)

end TowerInstances


end LanglandsTunnell
