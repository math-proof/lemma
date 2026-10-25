import Mathlib

set_option autoImplicit false

universe u v

namespace groupCohomology

namespace Kummer

section Unbundled

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

end Unbundled

section RepLevel

variable {K L : Type} [Field K] [Field L] [Algebra K L]

noncomputable abbrev kummerRep (K L : Type) [Field K] [Field L] [Algebra K L] (p : ℕ) :
    Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L)

variable {p : ℕ} {a : Kˣ} {α : Lˣ}

end RepLevel

end Kummer

end groupCohomology
