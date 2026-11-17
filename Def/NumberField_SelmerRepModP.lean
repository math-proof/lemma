import Mathlib

set_option autoImplicit false

noncomputable section

open scoped Pointwise

namespace NumberField.LevelArith

variable (E F : Type) [Field E] [Field F] [Algebra E F] (p : ℕ)

def unitsModPow : Type := Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range

abbrev unitsModPow.mk (x : Fˣ) : unitsModPow F p := (QuotientGroup.mk x : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range)

theorem unitsModPow.mk_surjective : Function.Surjective (unitsModPow.mk F p) := QuotientGroup.mk_surjective

local instance : CommGroup (unitsModPow F p) :=
  inferInstanceAs (CommGroup (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

theorem range_powMonoidHom_le_comap (σ : F ≃ₐ[E] F) :
    (powMonoidHom p : Fˣ →* Fˣ).range ≤ ((powMonoidHom p : Fˣ →* Fˣ).range).comap (MulDistribMulAction.toMonoidHom Fˣ σ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨σ • x, by rw [MulDistribMulAction.toMonoidHom_apply, powMonoidHom_apply, powMonoidHom_apply, smul_pow']⟩

def unitsModPowMap (σ : F ≃ₐ[E] F) : unitsModPow F p →* unitsModPow F p :=
  (QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom Fˣ σ) (range_powMonoidHom_le_comap E F p σ) :
    (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) →* (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

@[simp] theorem unitsModPowMap_mk (σ : F ≃ₐ[E] F) (x : Fˣ) :
    unitsModPowMap E F p σ (unitsModPow.mk F p x) = unitsModPow.mk F p (σ • x) :=
  rfl

end NumberField.LevelArith

end
