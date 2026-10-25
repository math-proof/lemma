-- Carved from Lemma/Definitions/Def_GroupCohomology_Kummer.lean: instance decls only.
import Mathlib
import Lemma.GroupCohomology.Kummer

set_option autoImplicit false

universe u v

namespace groupCohomology

namespace Kummer

section Unbundled

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

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
