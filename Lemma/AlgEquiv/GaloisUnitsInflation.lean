import Mathlib
import Def.GroupCohomology_GaloisUnitsInflation

set_option autoImplicit false

namespace groupCohomology

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [Normal K L]


@[simp] lemma unitsInflate₁_apply (c : (L ≃ₐ[K] L) → Additive (L)ˣ) (σ : Ω ≃ₐ[K] Ω) :
    unitsInflate₁ L c σ = Additive.ofMul
      (Units.map (algebraMap L Ω).toMonoidHom (Additive.toMul (c (AlgEquiv.restrictNormalHom L σ)))) :=
  rfl

@[simp] lemma unitsInflate₂_apply (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (σ τ : Ω ≃ₐ[K] Ω) :
    unitsInflate₂ L f (σ, τ) = Additive.ofMul
      (Units.map (algebraMap L Ω).toMonoidHom
        (Additive.toMul (f (AlgEquiv.restrictNormalHom L σ, AlgEquiv.restrictNormalHom L τ)))) :=
  rfl

lemma coe_toMul_unitsInflate₁ (c : (L ≃ₐ[K] L) → Additive (L)ˣ) (σ : Ω ≃ₐ[K] Ω) :
    ((Additive.toMul (unitsInflate₁ L c σ) : Ωˣ) : Ω)
      = ((Additive.toMul (c (AlgEquiv.restrictNormalHom L σ)) : (L)ˣ) : L) :=
  rfl

lemma coe_toMul_unitsInflate₂ (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (σ τ : Ω ≃ₐ[K] Ω) :
    ((Additive.toMul (unitsInflate₂ L f (σ, τ)) : Ωˣ) : Ω)
      = ((Additive.toMul (f (AlgEquiv.restrictNormalHom L σ, AlgEquiv.restrictNormalHom L τ)) : (L)ˣ) : L) :=
  rfl

end groupCohomology
