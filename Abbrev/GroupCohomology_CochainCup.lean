import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (p q : ℕ)

abbrev cochainCupFst (σ : Fin (p + q) → G) : Fin p → G := fun i => σ (Fin.castAdd q i)

abbrev cochainCupSnd (σ : Fin (p + q) → G) : Fin q → G := fun j => σ (Fin.natAdd p j)


end groupCohomology
