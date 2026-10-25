import Mathlib
import Instance.GaloisRep_CompletionBridge

set_option autoImplicit false

noncomputable section

open UniformSpace

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

abbrev Gal : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p


abbrev galAlgHom (σ : Gal p) : ℂ_[p] →ₐ[ℚ_[p]] ℂ_[p] :=
  MulSemiringAction.toAlgHom ℚ_[p] ℂ_[p] σ

end PadicComplex

end
