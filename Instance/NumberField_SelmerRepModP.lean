-- Carved from Lemma/Definitions/Def_NumberField_SelmerRepModP.lean: instance decls only.

module

public import Mathlib
public import Def.NumberField_SelmerRepModP

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Pointwise

namespace NumberField.LevelArith

section Selmer

variable (E F : Type) [Field E] [Field F] [Algebra E F] (p : ℕ)

-- Def already declared this name as a `local instance`, so it is visible here but
-- not in the typeclass table. Re-register it instead of redeclaring.
attribute [instance] instCommGroupUnitsModPow

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

end Selmer


end NumberField.LevelArith

end
