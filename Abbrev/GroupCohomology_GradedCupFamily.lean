import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G)

abbrev GradedCupFamily : Type u :=
  (p q : ℕ) → (groupCohomology A p →ₗ[k] groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) (p + q))

end groupCohomology
