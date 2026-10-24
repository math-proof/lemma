import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_LanglandsTunnell_C8Tower
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open Int
open NumberField LanglandsTunnell


/--
[LanglandsTunnell_finrank_fixFld_sylowH](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_finrank_fixFld_sylowH.lean)
-/
private lemma card_GL2_F3_aux : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  simp [ZMod.card, Fin.prod_univ_two]

@[path]
private lemma main
  [Field L] [NumberField L] [IsGalois ℚ L]
-- given
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
-- imply
  Module.finrank ℚ ↥(fixFld (sylowH e)) = 3 := by
-- proof
  have h16 : Module.finrank ↥(fixFld (sylowH e)) L = 16 := by
    rw [show fixFld (sylowH e) = IntermediateField.fixedField (sylowH e) from rfl,
      IntermediateField.finrank_fixedField_eq_card, card_sylowH]
  have h48 : Module.finrank ℚ L = 48 := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv, card_GL2_F3_aux]
  have htower := Module.finrank_mul_finrank ℚ ↥(fixFld (sylowH e)) L
  rw [h16, h48] at htower
  omega


-- created on 2026-10-24
