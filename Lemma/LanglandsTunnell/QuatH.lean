import Lemma.LanglandsTunnell.SylowH
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Def.LanglandsTunnell_QuatH
import Abbrev.LanglandsTunnell_QuatH

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField FLT.ExplicitLift LanglandsTunnell.Lift48
open scoped MatrixGroups

variable {L : Type} [Field L] [NumberField L]

theorem fixFld_le_fixFld_of_le {H H' : Subgroup (L ≃ₐ[ℚ] L)} (h : H' ≤ H) :
    fixFld H ≤ fixFld H' := by
  intro x hx
  rw [fixFld, FixedPoints.mem_intermediateField_iff] at hx ⊢
  exact fun g => hx ⟨g.1, h g.2⟩


theorem mem_detKer_iff (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) (γ : L ≃ₐ[ℚ] L) :
    γ ∈ detKer e ↔
      ((e γ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
  rw [detKer, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Units.val_eq_one]
  rfl


theorem quatH_le_sylowH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : quatH e ≤ sylowH e :=
  inf_le_left

theorem quatH_le_detKer (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : quatH e ≤ detKer e :=
  inf_le_right

theorem fixFld_sylowH_le_fixFld_quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) :
    fixFld (sylowH e) ≤ fixFld (quatH e) :=
  fixFld_le_fixFld_of_le (quatH_le_sylowH e)

theorem fixFld_detKer_le_fixFld_quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) :
    fixFld (detKer e) ≤ fixFld (quatH e) :=
  fixFld_le_fixFld_of_le (quatH_le_detKer e)


section SynthProbe

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))
noncomputable example : Algebra (𝓞 ↥(fixFld (sylowH e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example :
    Algebra.IsIntegral (𝓞 ↥(fixFld (sylowH e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example : Algebra (𝓞 ↥(fixFld (detKer e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example :
    Algebra.IsIntegral (𝓞 ↥(fixFld (detKer e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance

end SynthProbe

end LanglandsTunnell
