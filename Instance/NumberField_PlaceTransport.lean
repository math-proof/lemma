-- Carved from Lemma/Definitions/Def_NumberField_PlaceTransport.lean: instance decls only.
import Mathlib

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace NumberField.PlaceTransport


variable (E K : Type*) [Field E] [Field K] [Algebra E K]

noncomputable scoped instance instMulActionHeightOneSpectrum : MulAction (K ≃ₐ[E] K) (HeightOneSpectrum (𝓞 K)) where
  smul σ w := HeightOneSpectrum.comap (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹ : 𝓞 K →+* 𝓞 K)
    (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹).surjective w
  one_smul w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    show (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) 1⁻¹) x ∈ w.asIdeal ↔ x ∈ w.asIdeal
    rw [MulSemiringAction.toRingEquiv_apply, inv_one, one_smul])
  mul_smul σ τ w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    show (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) (σ * τ)⁻¹) x ∈ w.asIdeal ↔
      (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) τ⁻¹) ((MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹) x) ∈ w.asIdeal
    rw [MulSemiringAction.toRingEquiv_apply, MulSemiringAction.toRingEquiv_apply, MulSemiringAction.toRingEquiv_apply,
      mul_inv_rev, mul_smul])

variable {E K}

variable [NumberField K]

end NumberField.PlaceTransport
