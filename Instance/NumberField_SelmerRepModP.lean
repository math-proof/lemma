-- Carved from Lemma/Definitions/Def_NumberField_SelmerRepModP.lean: instance decls only.
import Mathlib
import Instance.NumberField_LevelArithmeticModP
import Lemma.NumberField.SelmerRepModP

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped NumberField NumberField.LevelArith Pointwise

namespace NumberField.LevelArith

section Selmer

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]

instance instCommGroupUnitsModPow : CommGroup (unitsModPow F p) :=
  inferInstanceAs (CommGroup (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

scoped instance instMulDistribMulActionUnitsModPow : MulDistribMulAction (F ≃ₐ[E] F) (unitsModPow F p) where
  smul σ := unitsModPowMap E F p σ
  one_smul q := by
    obtain ⟨x, rfl⟩ := unitsModPow.mk_surjective F p q
    exact congrArg (unitsModPow.mk F p) (one_smul (F ≃ₐ[E] F) x)
  mul_smul σ τ q := by
    obtain ⟨x, rfl⟩ := unitsModPow.mk_surjective F p q
    exact congrArg (unitsModPow.mk F p) (mul_smul σ τ x)
  smul_mul σ a b := map_mul (unitsModPowMap E F p σ) a b
  smul_one σ := map_one (unitsModPowMap E F p σ)

scoped instance instModuleZModSelmer : Module (ZMod p) (selmerRepInt E F S p) := AddCommGroup.zmodModule (nsmul_selmer_eq_zero E F S p)

end Selmer


end NumberField.LevelArith

end
