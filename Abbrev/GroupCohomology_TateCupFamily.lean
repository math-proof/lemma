import Mathlib
import Abbrev.GroupCohomology_TateCohomology

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace Rep

section family

variable (k G : Type u) [CommRing k] [Group G] [Fintype G]

abbrev TateCupFamily : Type (u + 1) :=
  ∀ (A B : Rep.{u} k G) (p q r : ℤ), p + q = r →
    (A.tateCohomology p →ₗ[k] B.tateCohomology q →ₗ[k] (A ⊗ B).tateCohomology r)

end family
end Rep
