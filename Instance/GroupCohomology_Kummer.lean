-- Carved from Lemma/Definitions/Def_GroupCohomology_Kummer.lean: instance decls only.

module

public import Mathlib

@[expose] public section

set_option autoImplicit false

universe u v

namespace groupCohomology

namespace Kummer

section Unbundled

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

private lemma val_smul_units (σ : L ≃ₐ[K] L) (α : Lˣ) : ((σ • α : Lˣ) : L) = σ (α : L) :=
  rfl

private lemma smul_units_pow (σ : L ≃ₐ[K] L) (x : Lˣ) (n : ℕ) : σ • (x ^ n) = (σ • x) ^ n := by
  ext
  simp only [val_smul_units, Units.val_pow_eq_pow_val, map_pow]

private lemma smul_mem_rootsOfUnity {p : ℕ} (σ : L ≃ₐ[K] L) {ζ : Lˣ} (hζ : ζ ∈ rootsOfUnity p L) :
    σ • ζ ∈ rootsOfUnity p L := by
  rw [mem_rootsOfUnity] at hζ ⊢
  rw [← smul_units_pow, hζ, smul_one]

instance instMulDistribMulActionRootsOfUnity (p : ℕ) :
    MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L) where
  smul σ ζ := ⟨σ • (ζ : Lˣ), smul_mem_rootsOfUnity σ ζ.2⟩
  one_smul ζ := Subtype.ext (one_smul _ (ζ : Lˣ))
  mul_smul σ τ ζ := Subtype.ext (mul_smul σ τ (ζ : Lˣ))
  smul_mul σ ζ η := Subtype.ext (smul_mul' σ (ζ : Lˣ) (η : Lˣ))
  smul_one σ := Subtype.ext (smul_one σ)

end Unbundled


end Kummer

end groupCohomology
