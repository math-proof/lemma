import Mathlib
import Structure.ExtCitation_AdmissibleExtension

set_option autoImplicit false

namespace ExtCitation

open ValuationSubring

variable (p : ℕ) [Fact p.Prime]
variable (V : Type) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

structure IsAdmissibleExtensionCts (C : Submodule (ZMod p) V) : Prop
    extends IsAdmissibleExtension p V C where

  open_kernel : IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | ∀ v : V, σ • v = v}


variable {p V} in


end ExtCitation
