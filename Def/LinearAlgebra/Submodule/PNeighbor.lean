/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Submodule/PNeighbor.lean -/

import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.SetTheory.Cardinal.Finite
/-!
# Kneser p-neighbors

This module defines the symmetric `p`-neighbor relation for two lattices
represented as submodules of a common ambient module.
-/


namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Two submodules are `p`-neighbors when `p` is prime and their intersection
has index `p` in each of them. -/
def ArePNeighbors (p : ℕ) (L₁ L₂ : Submodule R M) : Prop :=
  Nat.Prime p ∧
    Nat.card (L₁ ⧸ Submodule.comap L₁.subtype (L₁ ⊓ L₂)) = p ∧
    Nat.card (L₂ ⧸ Submodule.comap L₂.subtype (L₁ ⊓ L₂)) = p

end Submodule
