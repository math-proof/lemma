-- Carved from Lemma/Definitions/Def_LanglandsTunnell_QuatH.lean: instance decls only.
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField FLT.ExplicitLift LanglandsTunnell.Lift48
open scoped MatrixGroups

variable {L : Type} [Field L] [NumberField L]


instance detKer_normal (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : (detKer e).Normal := by
  unfold detKer; infer_instance


section TowerInstances

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))

noncomputable instance algebra_fixFldSylowH_fixFldQuatH :
    Algebra ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) :=
  (IntermediateField.inclusion (fixFld_sylowH_le_fixFld_quatH e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldSylowH_fixFldQuatH :
    IsScalarTower ℚ ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldSylowH_fixFldQuatH_L :
    IsScalarTower ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_sylowH_le_fixFld_quatH e) x).symm)

noncomputable instance algebra_fixFldDetKer_fixFldQuatH :
    Algebra ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) :=
  (IntermediateField.inclusion (fixFld_detKer_le_fixFld_quatH e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldDetKer_fixFldQuatH :
    IsScalarTower ℚ ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldDetKer_fixFldQuatH_L :
    IsScalarTower ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_detKer_le_fixFld_quatH e) x).symm)

end TowerInstances


end LanglandsTunnell
